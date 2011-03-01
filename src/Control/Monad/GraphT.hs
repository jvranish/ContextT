{-# LANGUAGE GeneralizedNewtypeDeriving
           , RankNTypes
           #-}
 
module Control.Monad.GraphT where

import Data.Maybe
import Data.Foldable
import Data.Traversable

import Control.Applicative
import Control.Monad.State hiding (mapM_, mapM, forM)
import Control.Monad.Cont hiding (mapM_, mapM, forM)

import qualified Control.Monad.ContextT as ContextT

import Prelude hiding (elem, and, concat, mapM, mapM_)


newtype GraphT s f m a = GraphT { unGraphT :: ContextT.ContextT s (f (GraphRef s f)) m a }
 deriving (Monad, MonadFix, MonadTrans, Applicative, Alternative, Functor, MonadPlus, MonadCont, MonadIO)

newtype GraphRef s f = GraphRef { unGraphRef :: ContextT.ContextRef s (f (GraphRef s f)) }

runGraphT :: (Monad m) => (forall s. GraphT s f m a) -> m a
runGraphT m = unsafeRunGraphT m

unsafeRunGraphT :: (Monad m) => GraphT s f m a -> m a
unsafeRunGraphT m = ContextT.unsafeRunContextT $ unGraphT m

newRef :: (Monad m) => f (GraphRef s f) -> GraphT s f m (GraphRef s f)
newRef a = liftM GraphRef $ GraphT $ ContextT.newRef a

readRef :: (Monad m) => GraphRef s f -> GraphT s f m (f (GraphRef s f))
readRef (GraphRef ref) = GraphT $ ContextT.readRef ref

writeRef :: (Monad m) => GraphRef s f -> f (GraphRef s f) -> GraphT s f m ()
writeRef (GraphRef ref) a = GraphT $ ContextT.writeRef ref a

subsRef :: (Monad m) => GraphRef s f -> GraphRef s f -> GraphT s f m ()
subsRef (GraphRef a) (GraphRef b) = GraphT $ ContextT.subsRef a b

subsRefs :: (Monad m) => [GraphRef s f] -> GraphRef s f -> GraphT s f m ()
subsRefs xs (GraphRef ref) = GraphT $ ContextT.subsRefs (fmap unGraphRef xs) ref

refEq :: (Monad m) => GraphRef s f -> GraphRef s f -> GraphT s f m Bool
refEq (GraphRef a) (GraphRef b) = GraphT $ ContextT.refEq a b

unsafeCastRef :: (Functor f) => (f (GraphRef s' g) -> g (GraphRef s' g)) -> GraphRef s f -> GraphRef s' g
unsafeCastRef f (GraphRef (ContextT.UnsafeContextRef ref a)) = GraphRef $ ContextT.UnsafeContextRef ref (f (fmap (unsafeCastRef f) a))

forkContext :: (Monad m, Functor f, Foldable t, Functor t) => t (GraphRef s f) -> (forall s'. t (GraphRef s' f) -> GraphT s' f m b) -> GraphT s f m b  
forkContext refs f = forkMappedContext refs id f
  
  

-- #TODO  check to see if the f needs to be polymorphic (I think it might need to be.. maybe not)
--forkMappedContext :: (Monad m, Functor f, Foldable t, Functor t) => t (GraphRef s f) -> (f (GraphRef s' g) -> g (GraphRef s' g)) -> (forall s'. t (GraphRef s' g) -> GraphT s' g m b) -> GraphT s f m b
forkMappedContext :: (Monad m, Functor f, Foldable t, Functor t) => t (GraphRef s f) -> (forall a. f a -> g a) -> (forall s'. t (GraphRef s' g) -> GraphT s' g m b) -> GraphT s f m b
forkMappedContext refs f g = do
  GraphT $ mapM_ ContextT.unsafeLookupRef (fmap unGraphRef refs) -- force ref commit
  context <- GraphT $ ContextT.UnsafeContextT $  get
  GraphT $ ContextT.UnsafeContextT $ lift $ evalStateT (ContextT.unsafeUnContextT $ unGraphT $ g $ fmap (unsafeCastRef f) refs) (fmap (f . fmap (unsafeCastRef f))  context)


refElem :: (Monad m, Foldable g) => GraphRef s f -> g (GraphRef s f) -> GraphT s f m Bool
refElem ref t = refElem' $ toList t
  where
    refElem' []     = return False
    refElem' (x:xs) = do
      yep <- refEq ref x
      case yep of
        True  -> return True
        False -> refElem' xs

lookupRef :: (Monad m) => GraphRef s f -> [(GraphRef s f, a)] -> GraphT s f m (Maybe a)
lookupRef _ []            = return Nothing
lookupRef ref ((x,y):xys) = do
  yep <- refEq ref x
  case yep of
    True  -> return $ Just y
    False -> lookupRef ref xys
    

copySubGraph :: (MonadFix m, Traversable f, Functor f) => GraphRef s f -> GraphT s f m (GraphRef s f)
copySubGraph ref = do
  relevantNodes <- reachable ref
  lookupNew <- mfix $ \lookupNew -> do
    newNodes <- forM relevantNodes $ \x -> do
      newValue <- readRef x
      newRef =<< mapM lookupNew newValue
    let lookupNew' a = liftM fromJust $ lookupRef a $ zip relevantNodes newNodes
    return lookupNew'
  lookupNew ref

-- 
-- Check to see if a is reachable from b. Will return false if a == b unless there is a cycle
reachableFrom :: (Foldable f, Monad m) => GraphRef s f -> GraphRef s f -> GraphT s f m Bool
reachableFrom a b = refElem a =<< liftM concat . mapM reachable =<< return . toList =<< readRef b
  
-- The returned list always includes the original reference
reachable :: (Foldable f, Monad m) => GraphRef s f -> GraphT s f m [GraphRef s f]
reachable ref = reachable' [] ref
reachable' :: (Monad m, Foldable f) => [GraphRef s f] -> GraphRef s f -> GraphT s f m [GraphRef s f]
reachable' xs ref= do
  alreadyFound <- refElem ref xs
  case alreadyFound of
    True -> return []
    False -> do
      x <- readRef ref
      xs' <- liftM concat $ mapM (reachable' (ref:xs)) $ toList x
      return (ref:xs')

graphEq :: (Functor f, Eq (f ()), Foldable f, Monad m) => GraphRef s f -> GraphRef s f -> GraphT s f m Bool
graphEq aRef' bRef' = forkContext [aRef', bRef'] $ \[a', b'] -> let 
    graphEq' aRef bRef = do
      eq <- refEq aRef bRef
      case eq of
        True -> return True
        False -> do 
          a <- readRef aRef
          b <- readRef bRef
          case headEq a b of 
            False -> return False
            True -> do
              subsRef aRef bRef
              liftM and $ zipWithM graphEq' (toList a) (toList b)
    unitize x = fmap (const ()) x
    headEq a b = unitize a == unitize b
  in graphEq' a' b'
  
  
