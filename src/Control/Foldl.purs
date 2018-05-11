module Foldl where

import Prelude

import Control.Apply (lift2)
import Control.Comonad (class Comonad, duplicate)
import Control.Extend (class Extend)
import Data.Array ((:))
import Data.Const (Const(..))
import Data.Either (Either(..), either)
import Data.Exists (Exists, mkExists, runExists)
import Data.Foldable as F
import Data.Functor.Contravariant (class Contravariant, cmap)
import Data.Identity (Identity)
import Data.List as L
import Data.List.Lazy as LL
import Data.Map as M
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Monoid (class Monoid, mempty)
import Data.Monoid.Dual (Dual(..))
import Data.Monoid.Endo (Endo(..))
import Data.Newtype (class Newtype, over, unwrap)
import Data.Profunctor (class Profunctor, dimap)
import Data.Profunctor.Choice (class Choice, right)
import Data.Set as S
import Data.StrMap as StrMap
import Data.Traversable (class Traversable, mapAccumL)
import Data.Tuple (Tuple(..))

data Tuple3 a b c = Tuple3 a b c

instance showTuple3 :: (Show a, Show b, Show c) => Show (Tuple3 a b c) where
  show (Tuple3 a b c) = "Tuple3 " <> show a <> " " <> show b <> " " <> show c

type Handler a b = forall x. (b -> Const (Dual (Endo x)) b) -> a -> Const (Dual (Endo x)) a
type HandlerM m a b = forall x. (b -> Const (Dual (EndoM m x)) b) -> a -> Const (Dual (EndoM m x)) a

newtype EndoM m a = EndoM (a -> m a)

derive instance newtypeEndoM :: Newtype (EndoM m a) _

instance semigroupEndoM :: Monad m => Semigroup (EndoM m a) where
  append (EndoM f) (EndoM g) = EndoM (f <=< g)

instance monoidEndoM :: Monad m => Monoid (EndoM m a) where
  mempty = EndoM pure

newtype FoldF a b x = FoldF { step :: x -> a -> x, begin :: x, done :: x -> b }
derive instance newtypeFoldF :: Newtype (FoldF a b x) _

newtype Fold a b = Fold(Exists(FoldF a b))
derive instance newtypeFold :: Newtype (Fold a b) _

mkFoldF :: forall a b x. (x -> a -> x) -> x -> (x -> b) -> FoldF a b x
mkFoldF step begin done = FoldF { step, begin, done }

mkFold :: forall a b x. (x -> a -> x) -> x -> (x -> b) -> Fold a b
mkFold step begin = Fold <<< mkExists <<< mkFoldF step begin

leftDefault :: forall p a b c. Profunctor p => Choice p => p a c -> p (Either a b) (Either c b)
leftDefault = dimap (either Right Left) (either Right Left) <<< right

instance semiringFold :: (Semiring a, Semiring b) => Semiring (Fold a b) where
  add = lift2 (+)
  zero = pure zero
  mul = lift2 (*)
  one = pure one
  
instance ringFold :: (Ring a, Ring b) => Ring (Fold a b) where
  sub = lift2(-)

instance commutativeRingFold :: (CommutativeRing a, CommutativeRing b) => CommutativeRing (Fold a b)

instance euclideanRingFold :: (EuclideanRing a, EuclideanRing b) => EuclideanRing (Fold a b) where
  degree = degree
  div = lift2 (/)
  mod = lift2 mod

instance divisionRingFold :: (DivisionRing a, DivisionRing b) => DivisionRing (Fold a b) where
  recip = map recip  

instance semigroupFold :: Monoid b => Semigroup (Fold a b) where
  append = lift2 (<>)

instance monoidFold :: Monoid b => Monoid (Fold a b) where
  mempty = pure mempty 

instance functorFold :: Functor (Fold a) where
  map f = over Fold $ runExists \(FoldF p) -> mkExists $ mkFoldF p.step p.begin (f <<< p.done)

instance applyFold :: Apply (Fold a) where
  apply (Fold x) (Fold y) = runExists 
    (\(FoldF p1) -> 
      runExists 
        (\(FoldF p2) ->
          let step (Tuple xL xR) a = Tuple (p1.step xL a) (p2.step xR a)
              begin = Tuple p1.begin p2.begin
              done (Tuple xL xR) = p1.done xL (p2.done xR)
          in mkFold step begin done   
        ) y) x 

instance applicativeFold :: Applicative (Fold a) where
  pure b = mkFold (\_ _ -> unit) unit (\_ -> b)

instance profunctorFold :: Profunctor Fold where
  dimap f g = premap f <<< map g
  
instance choiceFold :: Choice Fold where
  right = over Fold $ runExists \(FoldF p) -> mkExists $ mkFoldF (lift2 p.step) (Right p.begin) (map p.done)
  left x = leftDefault x

instance extendFold :: Extend (Fold a) where
  extend f = map f <<< duplicate
    --over Fold (runExists \(FoldF p) -> mkExists $ mkFoldF p.step p.begin (\x -> f $ mkFold p.step x p.done))

instance comonadFold :: Comonad (Fold a) where
  extract = unwrap >>> runExists (\(FoldF p) -> p.done p.begin)

fold :: forall f a b. F.Foldable f => Fold a b -> f a -> b
fold (Fold r) as = r # runExists \(FoldF p) -> F.foldr (\a k x -> k $ p.step x a) p.done as p.begin

sum :: Fold Int Int
sum = mkFold (+) 0 id

premap :: forall a b r. (a -> b) -> Fold b r -> Fold a r
premap f = over Fold $ runExists \(FoldF p) -> mkExists $ mkFoldF (\x a -> p.step x (f a)) p.begin p.done

groupBy :: forall g a r. Ord g => (a -> g) -> Fold a r -> Fold a (M.Map g r)
groupBy grouper = over Fold $ runExists \(FoldF p) -> mkExists $ mkFoldF (\m a -> M.alter (\o -> Just (p.step (fromMaybe p.begin o) a)) (grouper a) m) mempty (map p.done)

scan :: forall a b. Fold a b -> (Array a) -> (Array b)
scan (Fold r) as = r # runExists \(FoldF p) -> F.foldr (\a k x -> p.done x:(k $ p.step x a)) (\x -> p.done x:[]) as p.begin

length :: forall a. Fold a Int
length = mkFold (\n _ -> n + 1) 0 id

mconcat :: forall a. Monoid a => Fold a a
mconcat = mkFold (<>) mempty id

foldMap :: forall w a b. Monoid w => (a -> w) -> (w -> b) -> Fold a b
foldMap to = mkFold (\x a -> x <> (to a)) mempty

_Fold1 :: forall a. (a -> a -> a) -> Fold a (Maybe a)
_Fold1 step = mkFold step_ Nothing id
  where
    step_ mx a = maybe (Just a) (\x -> Just $ step x a) mx

head :: forall a. Fold a (Maybe a)
head = _Fold1 const

last :: forall a. Fold a (Maybe a)
last = _Fold1 (flip const)

lastDef :: forall a. a -> Fold a a
lastDef a = mkFold (\_ a' -> a') a id

null :: forall a. Fold a Boolean
null = mkFold (\_ _ -> false) true id

all :: forall a. (a -> Boolean) -> Fold a Boolean
all predicate = mkFold (\x a -> x && predicate a) true id

any :: forall a. (a -> Boolean) -> Fold a Boolean
any predicate = mkFold (\x a -> x || predicate a) false id

product :: Fold Int Int
product = mkFold (*) 1 id

mean :: Fold Int Int
mean = mkFold step begin done
  where
    begin = Tuple 0 0
    step (Tuple x n) y = Tuple ((x * n + y) / (n + 1)) (n + 1)
    done (Tuple x _) = x

variance :: Fold Int Int
variance = mkFold step begin done
  where
    begin = Tuple3 0 0 0
    step (Tuple3 n mean_ m2) x = Tuple3 n' mean' m2'
      where
        n'     = n + 1
        mean'  = (n * mean_ + x) / (n + 1)
        delta  = x - mean_
        m2'    = m2 + delta * delta * n / (n + 1)
    done (Tuple3 n _ m2) = m2 / n

maximum :: forall a. Ord a => Fold a (Maybe a)
maximum = _Fold1 max

maximumBy :: forall a. (a -> a -> Ordering) -> Fold a (Maybe a)
maximumBy cmp = _Fold1 max'
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y

minimum :: forall a. Ord a => Fold a (Maybe a)
minimum = _Fold1 min

minimumBy :: forall a. (a -> a -> Ordering) -> Fold a (Maybe a)
minimumBy cmp = _Fold1 min'
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x

elem :: forall a. Eq a => a -> Fold a Boolean
elem a = any (a == _)

notElem :: forall a. Eq a => a -> Fold a Boolean
notElem a = all (a /= _)

find :: forall a. (a -> Boolean) -> Fold a (Maybe a)
find predicate = mkFold step Nothing id
  where
    step x a = case x of
        Nothing -> if predicate a then Just a else Nothing
        _        -> x

lookup :: forall a b. Eq a => a -> Fold (Tuple a b) (Maybe b)
lookup a0 = mkFold step Nothing id
  where
    step x (Tuple a b) = case x of
      Nothing -> if a == a0
        then Just b
        else Nothing
      _ -> x

elemIndex :: forall a. Eq a => a -> Fold a (Maybe Int)
elemIndex a = findIndex (a == _)

findIndex :: forall a. (a -> Boolean) -> Fold a (Maybe Int)
findIndex predicate = mkFold step (Left 0) (either (const Nothing) Just)
  where
    step x a = case x of
        Left i -> if predicate a then Right i else Left (i + 1)
        _       -> x

index :: forall a. Int -> Fold a (Maybe a)
index i = mkFold step (Left 0) done
  where
    step x a = case x of
        Left  j -> if i == j then Right a else Left (j + 1)
        _        -> x
    done x = case x of
        Left  _ -> Nothing
        Right a -> Just a

purely :: forall a b r. (forall x . (x -> a -> x) -> x -> (x -> b) -> r) -> Fold a b -> r
purely f = unwrap >>> runExists \(FoldF p) -> f p.step p.begin p.done

purely_ :: forall a b. (forall x . (x -> a -> x) -> x -> x) -> Fold a b -> b
purely_ f = unwrap >>> runExists \(FoldF p) -> p.done (f p.step p.begin)

filtered :: forall m a. Monoid m => (a -> Boolean) -> (a -> m) -> a -> m
filtered p k x
  | p x = k x
  | otherwise = mempty

folded :: forall a f t. Contravariant f => Applicative f => F.Foldable t => (a -> f a) -> (t a -> f (t a))
folded k = cmap (\_ -> unit) <<< F.traverse_ k

foldOver :: forall s a b. Handler s a -> Fold a b -> s -> b
foldOver l = unwrap >>> runExists \(FoldF p) -> p.done <<< flip unwrap p.begin <<< unwrap <<< unwrap <<< l (Const <<< Dual <<< Endo <<< flip p.step)

handles :: forall a b r. Handler a b -> Fold b r -> Fold a r
handles k = over Fold $ runExists \(FoldF p) -> 
  let step' = flip (unwrap <<< unwrap <<< unwrap <<< k (Const <<< Dual <<< Endo <<< flip p.step)) 
  in mkExists $ mkFoldF step' p.begin p.done

prefilter :: forall a r. (a -> Boolean) -> Fold a r -> Fold a r
prefilter f = over Fold $ runExists \(FoldF p) -> 
  let step' x a = if f a then p.step x a else x 
  in mkExists $ mkFoldF step' p.begin p.done

mMap :: forall a b. Ord a => Fold (Tuple a b) (M.Map a b)
mMap = mkFold step begin done
  where
    begin = mempty
    step m (Tuple k v) = M.insert k v m
    done = id

set :: forall a. Ord a => Fold a (S.Set a)
set = mkFold (flip S.insert) S.empty id

strMap :: forall a. Semigroup a => Fold (Tuple String a) (StrMap.StrMap a)
strMap = mkFold step begin done
  where
    begin = mempty
    step m (Tuple k v) = StrMap.insert k v m
    done = id

eqNub :: forall a. Eq a => Fold a (Array a)
eqNub = mkFold step (Tuple [] id) fin
  where
    step (Tuple known r) a = if F.elem a known
      then Tuple known r
      else Tuple (a : known) (r <<< (a : _))
    fin (Tuple _ r) = r []

nub :: forall a. Ord a => Fold a (Array a)
nub = mkFold step (Tuple S.empty id) fin
  where
    step (Tuple s r) a = if S.member a s
      then Tuple s r
      else Tuple (S.insert a s) (r <<< (a : _))
    fin (Tuple _ r) = r []

revArray :: forall a. Fold a (Array a)
revArray = mkFold (\x a -> a:x) [] id

array :: forall a. Fold a (Array a)
array = mkFold (\x a -> x <<< (a:_)) id (_ $ [])

revList :: forall a. Fold a (L.List a)
revList = mkFold (\x a -> a L.: x) L.Nil id

list :: forall a. Fold a (L.List a)
list = mkFold (\x a -> x <<< (a L.: _)) id (_ $ L.Nil)

revLazyList :: forall a. Fold a (LL.List a)
revLazyList = mkFold (\x a -> a LL.: x) LL.nil id

lazyList :: forall a. Fold a (LL.List a)
lazyList = mkFold (\x a -> x <<< (a LL.: _)) id (_ $ LL.nil)

newtype FoldFM m a b x = FoldFM { step:: x -> a -> m x, begin:: m x, done:: x -> m b }
derive instance newtypeFoldFM :: Newtype (FoldFM m a b x) _

newtype FoldM m a b = FoldM (Exists (FoldFM m a b))
derive instance newtypeFoldM :: Newtype (FoldM m a b) _

mkFoldFM :: forall m a b x. (x -> a -> m x) -> m x -> (x -> m b) -> FoldFM m a b x
mkFoldFM f g h = FoldFM { step: f, begin: g, done: h }

mkFoldM :: forall m a b x. (x -> a -> m x) -> m x -> (x -> m b) -> FoldM m a b
mkFoldM f g = FoldM <<< mkExists <<< mkFoldFM f g

premapM :: forall m a b r. (a -> b) -> FoldM m b r -> FoldM m a r
premapM f = over FoldM $ runExists \(FoldFM p) -> let step' x a = p.step x (f a) in mkExists $ mkFoldFM step' p.begin p.done

instance functorFoldM :: Monad m => Functor (FoldM m a) where
  map f = over FoldM $ runExists \(FoldFM p) -> mkExists $ mkFoldFM p.step p.begin (map f <<< p.done)

instance applyFoldM :: Monad m => Apply (FoldM m a) where
  apply (FoldM x) (FoldM y) = runExists 
    (\(FoldFM p1) ->
      runExists 
        (\(FoldFM p2) -> 
          let step (Tuple xL xR) a = do
                  xL' <- p1.step xL a
                  xR' <- p2.step xR a
                  pure $ Tuple xL' xR'
              begin = do
                  xL <- p1.begin
                  xR <- p2.begin
                  pure $ Tuple xL xR
              done (Tuple xL xR) = do
                  f <- p1.done xL
                  x <- p2.done xR
                  pure $ f x
          in mkFoldM step begin done
        ) y ) x

instance applicativeFoldM :: Monad m => Applicative (FoldM m a) where
  pure b = mkFoldM (\_ _ -> pure unit) (pure unit) (\_ -> pure b)

instance profunctorFoldM :: Monad m => Profunctor (FoldM m) where
  dimap f g = premapM f <<< map g

instance semigroupFoldM :: (Monoid b, Monad m) => Semigroup (FoldM m a b) where
  append = lift2 (<>)

instance monoidFoldM :: (Monoid b, Monad m) => Monoid (FoldM m a b) where
  mempty = pure mempty

instance extendFoldM :: Monad m => Extend (FoldM m a) where
  extend f = map f <<< duplicateM
  --over FoldM $ runExists \(FoldFM p) -> mkExists $ mkFoldFM p.step p.begin (\x -> pure $ f $ mkFoldM p.step (pure x) p.done)

foldOverM :: forall m s a b. Monad m => HandlerM m s a -> FoldM m a b -> s -> m b
foldOverM l = unwrap >>> runExists \(FoldFM p) s -> do
  b <- p.begin
  r <- (flip unwrap b <<< unwrap <<< unwrap <<< l (Const <<< Dual <<< EndoM <<< flip p.step)) s
  p.done r

handlesM :: forall m a b r. HandlerM m a b -> FoldM m b r -> FoldM m a r
handlesM k = over FoldM $ runExists \(FoldFM p) -> 
  let step' = flip (unwrap <<< unwrap <<< unwrap <<< k (Const <<< Dual <<< EndoM <<< flip p.step)) 
  in mkExists $ mkFoldFM step' p.begin p.done

prefilterM :: forall m a r. Monad m => (a -> m Boolean) -> FoldM m a r -> FoldM m a r
prefilterM f = over FoldM $ runExists \(FoldFM p) -> 
  let step' x a = do
        use <- f a
        if use then p.step x a else pure x
  in mkExists $ mkFoldFM step' p.begin p.done

duplicateM :: forall m a b. Applicative m => FoldM m a b -> FoldM m a (FoldM m a b)
duplicateM = over FoldM $ runExists \(FoldFM p) -> mkExists $ mkFoldFM p.step p.begin (\x -> pure (mkFoldM p.step (pure x) p.done))

hoists :: forall m n a b. (forall x . m x -> n x) -> FoldM m a b -> FoldM n a b
hoists phi = over FoldM $ runExists \(FoldFM p) -> mkExists $ mkFoldFM (\a b -> phi (p.step a b)) (phi p.begin) (phi <<< p.done)

simplify :: forall a b. FoldM Identity a b -> Fold a b
simplify = unwrap >>> runExists \(FoldFM p) -> mkFold (\x a -> unwrap (p.step x a)) (unwrap p.begin) (\x -> unwrap (p.done x))

generalize :: forall m a b. Monad m => Fold a b -> FoldM m a b
generalize = unwrap >>> runExists \(FoldF p) -> mkFoldM (\x a -> pure (p.step x a)) (pure p.begin) (\x -> pure (p.done x))

impurely_ :: forall m a b. Monad m => (forall x . (x -> a -> m x) -> m x -> m x) -> FoldM m a b -> m b
impurely_ f = unwrap >>> runExists \(FoldFM p) -> f p.step p.begin >>= p.done

impurely :: forall m a b r. (forall x . (x -> a -> m x) -> m x -> (x -> m b) -> r) -> FoldM m a b -> r
impurely f = unwrap >>> runExists \(FoldFM p) -> f p.step p.begin p.done

sink :: forall m w a. Monoid w => Monad m => (a -> m w) -> FoldM m a w
sink act = mkFoldM (\m a -> act a >>= pure <<< (m <> _)) (pure mempty) pure

mapM_ :: forall m a. Monad m => (a -> m Unit) -> FoldM m a Unit
mapM_ = sink

postscan :: forall t a b. Traversable t => Fold a b -> t a -> t b
postscan = unwrap >>> runExists \(FoldF p) as ->
  let r = mapAccumL (\x a -> {accum: (p.step x a), value: (p.done $ p.step x a)}) p.begin as in r.value 

foldM :: forall f m a b. F.Foldable f => Monad m => FoldM m a b -> f a -> m b
foldM f as = (runExists \(FoldFM p) -> p.begin >>= F.foldr (\a k x -> p.step x a >>= k) p.done as) $ unwrap f