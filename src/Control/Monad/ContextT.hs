{-# LANGUAGE GeneralizedNewtypeDeriving
           , RankNTypes
           , DeriveFunctor
           , DeriveFoldable
           , DeriveTraversable
           #-}
                    
module Control.Monad.ContextT where

import Data.Maybe
import Data.Foldable
import Data.Traversable 

import qualified Data.IntMap as IntMap

import Control.Applicative
import Control.Monad.State hiding (mapM_, mapM, forM)
import Control.Monad.Cont hiding (mapM_, mapM, forM)

import Prelude hiding (elem, and, concat, mapM, mapM_)

 -- This has no Eq, or Ord because they would basically never do what you expect.
 -- The value stored in the reference is only the initial value
data ContextRef s a = UnsafeContextRef Int a
  deriving (Show)

data ContextData t = ContextData Int (IntMap.IntMap Int) (IntMap.IntMap (t, [Int]))
  deriving (Functor, Foldable, Traversable)

-- safe to construct, unsafe to deconstruct
newtype ContextT s t m a = UnsafeContextT { unsafeUnContextT :: StateT (ContextData t) m a}
 deriving (Monad, MonadFix, MonadTrans, Applicative, Alternative, Functor, MonadPlus, MonadCont, MonadIO)
  
runContextT :: (Monad m) => (forall s. ContextT s t m a) -> m a
runContextT m = unsafeRunContextT m

unsafeRunContextT :: (Monad m) => ContextT s t m a -> m a
unsafeRunContextT m = evalStateT (unsafeUnContextT m) (ContextData 0 IntMap.empty IntMap.empty)

newRef :: (Monad m) => t -> ContextT s t m (ContextRef s t)
newRef a = UnsafeContextT $ do
  ContextData n x y <- get
  put $ ContextData (n + 1) x y
  return $ UnsafeContextRef n a

readRef :: (Monad m) => ContextRef s t -> ContextT s t m t
readRef (UnsafeContextRef ref a) = UnsafeContextT $ do
  ContextData _ x y <- get
  let value = do -- we don't call unsafeLookupRef here because we don't need to commit the ref here if it's not in the map
      valueIdx <- IntMap.lookup ref x
      liftM fst $ IntMap.lookup valueIdx y
  return $ case value of
      Just val -> val
      Nothing -> a
           
writeRef :: (Monad m) => ContextRef s t -> t -> ContextT s t m ()
writeRef ref a = do
  (valueIdx, _, otherKeys) <- unsafeLookupRef ref
  ContextData n x y <- UnsafeContextT $ get
  UnsafeContextT $ put $ ContextData n x (IntMap.insert valueIdx (a, otherKeys) y)


unsafeLookupRef :: (Monad m) => ContextRef s t -> ContextT s t m (Int, t, [Int])
unsafeLookupRef (UnsafeContextRef ref a) = UnsafeContextT $ do
  ContextData n x y <- get
  let result = do
      index <- IntMap.lookup ref x
      (value, keys) <- IntMap.lookup index y
      return (index, value, keys)
  case result of
    Just val -> return val
    Nothing -> do
      put $ ContextData n (IntMap.insert ref ref x) (IntMap.insert ref (a, [ref]) y)
      return (ref, a, [ref])

-- substitute a with b
subsRef :: (Monad m) => ContextRef s t -> ContextRef s t -> ContextT s t m ()
subsRef (UnsafeContextRef a _) (UnsafeContextRef b _) | a == b = return ()
subsRef aRef bRef = do
  (aIndex, _     , aKeys) <- unsafeLookupRef aRef
  (bIndex, bValue, bKeys) <- unsafeLookupRef bRef
  ContextData n x y <- UnsafeContextT $ get
  let affectedRefs = aKeys ++ bKeys
  let refUpdates = IntMap.fromList $ zip affectedRefs $ repeat bIndex
  let newX = IntMap.union refUpdates x
  let newY = IntMap.insert bIndex (bValue, affectedRefs) y
  case aIndex == bIndex of
    True -> return ()
    False -> UnsafeContextT $ put $ ContextData n newX newY
                       
subsRefs :: (Monad m) => [ContextRef s t] -> ContextRef s t -> ContextT s t m ()
subsRefs xs a = mapM_ (flip subsRef a) xs
  
refEq :: (Monad m) => ContextRef s t -> ContextRef s t -> ContextT s t m Bool
refEq (UnsafeContextRef a _) (UnsafeContextRef b _) | a == b = return True
refEq (UnsafeContextRef a _) (UnsafeContextRef b _) = UnsafeContextT $ do
  ContextData _ x _ <- get
  let maybeEqual = do
      aIndex <- IntMap.lookup a x
      bIndex <- IntMap.lookup b x
      return (aIndex == bIndex)
  case maybeEqual of
    Just r -> return r
    Nothing -> return False -- if either one is not commited yet, and the ref Id's themselves are not equal, then they're not equal

