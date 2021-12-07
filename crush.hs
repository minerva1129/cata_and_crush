{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Data.Functor.Constant
import Data.Functor.Identity
import Data.Functor.Sum
import Data.Functor.Product
import Data.Bifunctor

type Algebra f a = f a -> a

newtype WrappedBifunctor f a b = Wrap { unwrap :: f a b }
instance Bifunctor f => Functor (WrappedBifunctor f a) where
  fmap f (Wrap a) = Wrap (second f a)

newtype Mu f = Mu { unMu :: f (Mu f) }
newtype Tau f a = Tau { unTau :: Mu (WrappedBifunctor f a) }

cata :: Functor f => Algebra f a -> Mu f -> a
cata phi = phi . fmap (cata phi) . unMu

type K = Constant
type I = Identity
type (:+:) = Sum
type (:*:) = Product

instance Bifunctor f => Functor (Tau f) where
  fmap g = Tau . (cata (Mu . Wrap . first g . unwrap)) . unTau

newtype Biconstant a b c = Biconstant { getBiConstant :: a }
instance Bifunctor (Biconstant a) where
  bimap _ _ (Biconstant x) = Biconstant x

newtype ProjectionL f a b = ProjectionL { runProjectionLeft :: f a }
instance Functor f => Bifunctor (ProjectionL f) where
  bimap g _ (ProjectionL x) = ProjectionL (fmap g x)

newtype ProjectionR f a b = ProjectionR { runProjectionRight :: f b }
instance Functor f => Bifunctor (ProjectionR f) where
  bimap _ h (ProjectionR x) = ProjectionR (fmap h x)

data Bisum f g a b = BiinL (f a b) | BiinR (g a b)
instance (Bifunctor f, Bifunctor g) => Bifunctor (Bisum f g) where
  bimap f g (BiinL x) = BiinL (bimap f g x)
  bimap f g (BiinR y) = BiinR (bimap f g y)

data Biproduct f g a b = Bipair (f a b) (g a b)
instance (Bifunctor f, Bifunctor g) => Bifunctor (Biproduct f g) where
  bimap f g (Bipair x y) = Bipair (bimap f g x) (bimap f g y)

type KK = Biconstant
type L = ProjectionL
type R = ProjectionR
type (:++:) = Bisum
type (:**:) = Biproduct

class Functor f => CrushableFunctor f where
  crush :: (a -> a -> a) -> a -> f a -> a

class Bifunctor f => CrushableBifunctor f where
  bicrush :: (a -> a -> a) -> a -> f a a -> a

-- CrushableFunctor :=
--   | Const *
--   | Identity
--   | Sum CrushableFunctor CrushableFunctor
--   | Prod CrushableFunctor CrushableFunctor
--   | Tau CrushableBiFunctor

instance CrushableFunctor (K a) where
  crush _ nu (Constant x) = nu

instance CrushableFunctor I where
  crush _ _ (Identity x) = x

instance (CrushableFunctor f, CrushableFunctor g) => CrushableFunctor (f :+: g) where
  crush op nu (InL x) = crush op nu x
  crush op nu (InR x) = crush op nu x

instance (CrushableFunctor f, CrushableFunctor g) => CrushableFunctor (f :*: g) where
  crush op nu (Pair x y) = op (crush op nu x) (crush op nu y)

instance CrushableBifunctor f => CrushableFunctor (Tau f) where
  crush op nu = cata (bicrush op nu . unwrap) . unTau

-- CrushableBiFunctor :=
--   | Const *
--   | ProjL CrushableFunctor
--   | ProjR CrushableFunctor
--   | Sum CrushableBiFunctor CrushableBiFunctor
--   | Prod CrushableBiFunctor CrushableBiFunctor

instance CrushableBifunctor (KK a) where
  bicrush _ nu (Biconstant x) = nu

instance CrushableFunctor f => CrushableBifunctor (L f) where
  bicrush op nu (ProjectionL x) = crush op nu x

instance CrushableFunctor f => CrushableBifunctor (R f) where
  bicrush op nu (ProjectionR x) = crush op nu x

instance (CrushableBifunctor f, CrushableBifunctor g) => CrushableBifunctor (f :++: g) where
  bicrush op nu (BiinL x) = bicrush op nu x
  bicrush op nu (BiinR x) = bicrush op nu x

instance (CrushableBifunctor f, CrushableBifunctor g) => CrushableBifunctor (f :**: g) where
  bicrush op nu (Bipair x y) = op (bicrush op nu x) (bicrush op nu y)

-- MaybeF = 1 + id
type MaybeF = (K ()) :+: I

none :: MaybeF a
none = InL (Constant ())

some :: a -> MaybeF a
some x = InR (Identity x)

-- ListF a = μ (1 + (a * id))
type ListF = Tau ((KK ()) :++: ((L I) :**: (R I)))

nil :: ListF a
nil = Tau (Mu (Wrap (BiinL (Biconstant ()))))

cons :: a -> ListF a -> ListF a
cons x xs = Tau (Mu (Wrap (BiinR (Bipair (ProjectionL (Identity x)) (ProjectionR (Identity (unTau xs)))))))

-- BinTreeF a = μ (a + (id * id))
type BinTreeF = Tau ((L I) :++: ((R I) :**: (R I)))

tip :: a -> BinTreeF a
tip x = Tau (Mu (Wrap (BiinL (ProjectionL (Identity x)))))

join :: BinTreeF a -> BinTreeF a -> BinTreeF a
join x y = Tau (Mu (Wrap (BiinR (Bipair (ProjectionR (Identity (unTau x))) (ProjectionR (Identity (unTau y)))))))

-- RoseTreeF a = μ (a * ListF) = μ (a * (\b -> μ (1 + (b * id))))
type RoseTreeF = Tau ((L I) :**: (R ListF))

fork :: a -> ListF (RoseTreeF a) -> RoseTreeF a
fork x xs = Tau (Mu (Wrap (Bipair (ProjectionL (Identity x)) (ProjectionR (fmap unTau xs)))))

sum_ :: CrushableFunctor f => f Int -> Int
sum_ = crush (+) 0

crushf :: CrushableFunctor f => (a -> a -> a) -> a -> (b -> a) -> f b -> a
crushf op nu g = crush op nu . fmap g

size :: CrushableFunctor f => f a -> Int
size = crushf (+) 0 (const 1)

elem_ :: (CrushableFunctor f, Eq a) => a -> f a -> Bool
elem_ e = crushf (||) False (== e)

flatten :: CrushableFunctor f => f a -> [a]
flatten = crushf (++) [] (\x -> [x])

crushM :: CrushableFunctor f => (a -> a -> a) -> f a -> Maybe a
crushM op = crushf opM Nothing Just
  where
  opM Nothing Nothing = Nothing
  opM (Just x) Nothing = Just x
  opM Nothing (Just y) = Just y
  opM (Just x) (Just y) = Just (op x y)

first_ :: CrushableFunctor f => f a -> Maybe a
first_ = crushM const

crushMf :: CrushableFunctor f => (a -> a -> a) -> (b -> a) -> f b -> Maybe a
crushMf op g = crushf opM Nothing (Just . g)
  where
  opM Nothing Nothing = Nothing
  opM (Just x) Nothing = Just x
  opM Nothing (Just y) = Just y
  opM (Just x) (Just y) = Just (op x y)

depth :: CrushableFunctor f => f a -> Maybe Int
depth = crushMf (\m n -> (max m n) + 1) (const 0)

binned :: CrushableFunctor f => f a -> Maybe (BinTreeF a)
binned = crushMf join tip

