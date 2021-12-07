{-# LANGUAGE DeriveFunctor #-}

type Algebra f a = f a -> a

-- F μF --inF-> μF
-- F μF <-outF- μF
newtype Mu f = Mu { unMu :: f (Mu f) }

-- F μF --inF-> μF
-- |            |
-- F cataφ      cataφ
-- |            |
-- v            v
-- FX --- φ --> X

cata :: Functor f => Algebra f a -> Mu f -> a
cata phi = phi . fmap (cata phi) . unMu

-- MaybeF = 1 + id
data MaybeF a = None | Some a deriving (Functor)
type Maybe_ a = MaybeF a

sumMaybe :: Maybe_ Int -> Int
sumMaybe None = 0
sumMaybe (Some n) = n

mapMaybe :: (a -> b) -> Maybe_ a -> Maybe_ b
mapMaybe _ None = None
mapMaybe f (Some x) = Some (f x)

elemMaybe :: Eq a => a -> (MaybeF a) -> Bool
elemMaybe e None = False
elemMaybe e (Some x) = e == x

-- ListF a = 1 + (a * id)
data ListF a x = Nil | Cons a x deriving (Functor)
type List a = Mu (ListF a)

sumList :: List Int -> Int
sumList = cata phi
  where
  phi Nil = 0
  phi (Cons m n) = m + n

mapList :: (a -> b) -> List a -> List b
mapList g = cata phi
  where
  phi Nil = Mu Nil
  phi (Cons x ys) = Mu (Cons (g x) ys)

elemList :: Eq a => a -> List a -> Bool
elemList e = cata phi
  where
  phi Nil = False
  phi (Cons x b) = e == x || b

-- BinTreeF a = a + (id * id)
data BinTreeF a x = Tip a | Join x x deriving (Functor)
type BinTree a = Mu (BinTreeF a)

sumBinTree :: BinTree Int -> Int
sumBinTree = cata phi
  where
  phi (Tip n) = n
  phi (Join m n) = m + n

mapBinTree :: (a -> b) -> BinTree a -> BinTree b
mapBinTree g = cata phi
  where
  phi (Tip x) = Mu (Tip (g x))
  phi (Join y1 y2) = Mu (Join y1 y2)

elemBinTree :: Eq a => a -> BinTree a -> Bool
elemBinTree e = cata phi
  where
  phi (Tip x) = e == x
  phi (Join lb rb) = lb || rb

-- RoseTreeF a = a * List = a * (μ ListF)
data RoseTreeF a x = Fork a (List x)
type RoseTree a = Mu (RoseTreeF a)

instance Functor (RoseTreeF a) where
  fmap g (Fork x ys) = Fork x (mapList g ys)

sumRoseTree :: RoseTree Int -> Int
sumRoseTree = cata phi
  where
  phi (Fork m l) = m + sumList l

mapRoseTree :: (a -> b) -> RoseTree a -> RoseTree b
mapRoseTree g = cata phi
  where
  phi (Fork x ys) = Mu (Fork (g x) ys)

anyList :: (a -> Bool) -> List a -> Bool
anyList p = cata phi
  where
  phi Nil = False
  phi (Cons x b) = p x || b

elemRoseTree :: Eq a => a -> RoseTree a -> Bool
elemRoseTree e = cata phi
  where
  phi (Fork x l) = e == x || anyList id l

