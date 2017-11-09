{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Prelude
import Test.QuickCheck
import Text.Show.Functions
import Data.Char (digitToInt)
import Data.Maybe (isNothing)
import Control.Monad

data List a = Nil | Cons a (List a) deriving (Show, Eq, Functor)

instance Arbitrary a => Arbitrary (List a) where
    arbitrary = toL <$> (arbitrary :: Arbitrary a => Gen [a])

instance CoArbitrary a => CoArbitrary (List a) where
    coarbitrary Nil = variant 0
    coarbitrary (Cons x xs) = variant 1 . coarbitrary (x,xs)

toL :: [a] -> List a
toL = foldr Cons Nil

fromL :: List a -> [a]
fromL = foldL (:) []

wrap :: a -> List a
wrap x = Cons x Nil

nil :: List a -> Bool
nil Nil = True
nil (Cons x xs) = False

foldL :: (a -> b -> b) -> b -> List a -> b
foldL f e Nil = e
foldL f e (Cons x xs) = f x (foldL f e xs)

-- exercise 3.2

mapL :: (a -> b) -> List a -> List b
mapL f = foldL (\x acc -> Cons (f x) acc) Nil

mapL' :: (a -> b) -> List a -> List b
mapL' f Nil = Nil
mapL' f (Cons x xs) = Cons (f x) (mapL' f xs)

prop_mapL :: (Int -> Int) -> List Int -> Bool
prop_mapL f xs = mapL f xs == mapL' f xs

appendL :: List a -> List a -> List a
appendL xs ys = foldL Cons ys xs

appendL' :: List a -> List a -> List a
appendL' Nil ys = ys
appendL' (Cons x xs) ys = Cons x (appendL' xs ys)

prop_appendL :: List Int -> List Int -> Bool
prop_appendL xs ys = appendL xs ys == appendL' xs ys

concatL :: List (List a) -> List a
concatL = foldL appendL Nil

concatL' :: List (List a) -> List a
concatL' Nil = Nil
concatL' (Cons xs xss) = appendL' xs (concatL' xss)

prop_concatL :: List (List Int) -> Bool
prop_concatL xss = concatL xss == concatL' xss

-- exercise 3.4

insert :: Ord a => a -> List a -> List a
insert y Nil = wrap y
insert y (Cons x xs)
    | y < x     = Cons y (Cons x xs)
    | otherwise = Cons x (insert y xs)

insert1 :: Ord a => a -> List a -> (List a, List a)
insert1 y = foldL f e
  where
    f x (xs, Cons y' ys) = if y < x
        then (Cons x xs, Cons y' (Cons x ys))
        else (Cons x xs, Cons x (Cons y' ys))
    e = (Nil, wrap y)

prop_insert1 :: Int -> Property
prop_insert1 y = forAll (fmap toL orderedList) $ \xs ->
    insert1 y xs == (xs, insert y xs)

-- exercise 3.5

paraL :: (a -> (List a,b) -> b) -> b -> List a -> b
paraL f e Nil = e
paraL f e (Cons x xs) = f x (xs, paraL f e xs)


insertP :: Ord a => a -> List a -> List a
insertP y = paraL f e
  where
    f x (xs, Cons y' ys) = if y < x
        then Cons y' (Cons x ys)
        else Cons x (Cons y' ys)
    e = wrap y

prop_insertP :: Int -> Property
prop_insertP y = forAll (fmap toL orderedList) $ \xs ->
    insertP y xs == insert y xs

-- exercise 3.6

unfoldL :: (b -> Bool) -> (b -> a) -> (b -> b) -> b -> List a
unfoldL p f g b = if p b then Nil else Cons (f b) (unfoldL p f g (g b))

unfoldL' :: (b -> Maybe (a,b)) -> b -> List a
unfoldL' f u = case f u of
    Nothing -> Nil
    Just (x,v) -> Cons x (unfoldL' f v)

myUnfoldL :: (b -> Bool) -> (b -> a) -> (b -> b) -> b -> List a
myUnfoldL p f g =
    unfoldL' (\b -> if p b then Nothing else Just (f b, g b))

takeL :: Int -> List a -> List a
takeL _ Nil = Nil
takeL 0 xs = Nil
takeL n (Cons x xs) = Cons x (takeL (n-1) xs)

prop_myUnfoldL :: (Int -> Bool) -> (Int -> Int) -> (Int -> Int) -> Int -> Bool
prop_myUnfoldL p f g b =
    takeL 100 (myUnfoldL p f g b) == takeL 100 (unfoldL p f g b)

fromJust :: Maybe a -> a
fromJust (Just x) = x

myUnfoldL' :: (b -> Maybe (a,b)) -> b -> List a
myUnfoldL' f =
    unfoldL (isNothing . f) (fst . fromJust . f) (snd . fromJust . f)

prop_myUnfoldL' :: (Int -> Maybe (Int,Int)) -> Int -> Bool
prop_myUnfoldL' f u = takeL 100 (myUnfoldL' f u) == takeL 100 (unfoldL' f u)

-- exercise 3.8

foldL' :: (Maybe (a,b) -> b) -> List a -> b
foldL' f Nil = f Nothing
foldL' f (Cons x xs) = f (Just (x, foldL' f xs))

myFoldL :: (a -> b -> b) -> b -> List a -> b
myFoldL f e =
    foldL' $ \xm -> case xm of
        Nothing -> e
        Just (x,y) -> f x y

prop_myFoldL :: (Int -> Int -> Int) -> Int -> List Int -> Bool
prop_myFoldL f e xs = myFoldL f e xs == foldL f e xs

myFoldL' :: (Maybe (a,b) -> b) -> List a -> b
myFoldL' f = foldL (\x y -> f (Just (x,y))) (f Nothing)

prop_myFoldL' :: (Maybe (Int,Int) -> Int) -> List Int -> Bool
prop_myFoldL' f xs = myFoldL' f xs == foldL' f xs

-- exercise 3.9

foldLargs :: (a -> b -> b) -> b -> (Maybe (a,b) -> b)
foldLargs f e = g
  where
    g Nothing = e
    g (Just (x,y)) = f x y

prop_foldLargs :: (Int -> Int -> Int) -> Int -> List Int -> Bool
prop_foldLargs f e xs = foldL f e xs == foldL' (foldLargs f e) xs

unfoldLargs :: (b -> Bool) -> (b -> a) -> (b -> b) -> (b -> Maybe (a,b))
unfoldLargs p f g = h
  where
    h b = if p b then Nothing else Just (f b, g b)

prop_unfoldLargs :: (Int -> Bool) -> (Int -> Int) -> (Int -> Int) -> Int -> Bool
prop_unfoldLargs p f g b =
    takeL 100 (unfoldL p f g b) == takeL 100 (unfoldL' (unfoldLargs p f g) b)

-- exercise 3.10

deleteL :: Eq a => a -> List a -> List a
deleteL y Nil = Nil
deleteL y (Cons x xs)
    | y == x = xs
    | otherwise = Cons x (deleteL y xs)

deleteL' :: Eq a => a -> List a -> List a
deleteL' y = paraL f e
  where
    f x (xs, ys) = if x == y then xs else Cons x ys
    e = Nil

prop_deleteL' :: Int -> List Int -> Bool
prop_deleteL' y xs = deleteL y xs == deleteL' y xs

-- exercise 3.11

delmin :: Ord a => List a -> Maybe (a, List a)
delmin Nil = Nothing
delmin xs = Just (y, deleteL y xs)
  where
    y = minimumL xs

minimumL :: Ord a => List a -> a
minimumL (Cons x xs) = foldL min x xs

delmin' :: Ord a => List a -> Maybe (a, List a)
delmin' = paraL f e
  where
    f x (xs,ym) = Just $ case ym of
        Nothing -> (x, Nil)
        Just (y,ys) -> if x <= y -- < gives different behaviour
            then (x, xs)
            else (y, Cons x ys)
    e = Nothing

prop_delmin' :: List Int -> Bool
prop_delmin' xs = delmin' xs == delmin xs

-- exercise 3.12

bubble :: Ord a => List a -> Maybe (a, List a)
bubble = foldL step Nothing
  where
    step x Nothing = Just (x, Nil)
    step x (Just (y,ys))
        | x < y = Just (x, Cons y ys)
        | otherwise = Just (y, Cons x ys)

bubble' :: Ord a => List a -> List a
bubble' = foldL step Nil
  where
    step x Nil = wrap x
    step x (Cons y ys)
        | x < y = Cons x (Cons y ys)
        | otherwise = Cons y (Cons x ys)

bsort :: Ord a => List a -> List a
bsort = unfoldL' bubble

bsort' :: Ord a => List a -> List a
bsort' = unfoldL nil (hd . bubble') (tl . bubble')
  where
    hd (Cons x xs) = x
    tl (Cons x xs) = xs

prop_bsort' :: List Int -> Bool
prop_bsort' xs = bsort' xs == bsort xs

-- exercise 3.13

insertU :: Ord a => a -> List a -> List a
insertU y xs = unfoldL' f (xs, Just y)
  where
    f (Nil, Nothing) = Nothing
    f (Nil, Just y) = Just (y, (Nil, Nothing))
    f (Cons x xs, Nothing) = Just (x, (xs, Nothing))
    f (Cons x xs, Just y) = if y < x
        then Just (y, (Cons x xs, Nothing))
        else Just (x, (xs, Just y))

prop_insertU :: Int -> List Int -> Bool
prop_insertU y xs = insertU y xs == insert y xs

-- exercise 3.14

apoL' :: (b -> Maybe (a, Either b (List a))) -> b -> List a
apoL' f u = case f u of
    Nothing -> Nil
    Just (x, Left v) -> Cons x (apoL' f v)
    Just (x, Right xs) -> Cons x xs

insertA :: Ord a => a -> List a -> List a
insertA y xs = apoL' f (xs, Just y)
  where
    f (Nil, Nothing) = Nothing
    f (Nil, Just y) = Just (y, Right Nil)
    f (Cons x xs, Nothing) = Just (x, Right xs)
    f (Cons x xs, Just y) = if y < x
        then Just (y, Left (Cons x xs, Nothing))
        else Just (x, Left (xs, Just y))

prop_insertA :: Int -> List Int -> Bool
prop_insertA y xs = insertU y xs == insert y xs

-- exercise 3.15

-- toBits :: List Char -> List Bool
-- toBits = unfoldL' g . foldL' f
--   where
--     f Nothing = (0,0)
--     f (Just (d,(n,y))) = (n+1, (digitToInt d)*10^n + y)
--     g (n,x) = if x == 0
--         then Nothing
--         else Just (toBit (x `mod` 2), (n,x `div` 2))
--     toBit 0 = False
--     toBit 1 = True

-- exercise 3.16

data Nat = Zero | Succ Nat deriving (Show, Eq)

instance Arbitrary Nat where
    arbitrary = fmap toN arbitrarySizedNatural

toN :: Int -> Nat
toN = unfoldN (== 0) (\n -> n-1)

fromN :: Nat -> Int
fromN = foldN 0 (+1)

foldN :: a -> (a -> a) -> Nat -> a
foldN z s Zero = z
foldN z s (Succ n) = s (foldN z s n)

foldN' :: (Maybe a -> a) -> Nat -> a
foldN' f Zero = f Nothing
foldN' f (Succ n) = f (Just (foldN' f n))

myFoldN :: a -> (a -> a) -> Nat -> a
myFoldN z s = foldN' f
  where
    f Nothing = z
    f (Just x) = s x

prop_myFoldN :: Int -> (Int -> Int) -> Nat -> Bool
prop_myFoldN z s n = foldN z s n == myFoldN z s n

myFoldN' :: (Maybe a -> a) -> Nat -> a
myFoldN' f = foldN (f Nothing) (f . Just)

prop_myFoldN' :: (Maybe Int -> Int) -> Nat -> Bool
prop_myFoldN' f n = foldN' f n == myFoldN' f n

-- exercise 3.18

addN :: Nat -> Nat -> Nat
addN n = foldN n Succ

prop_addN :: Nat -> Nat -> Bool
prop_addN n m = addN n m == toN (fromN n + fromN m)

mulN :: Nat -> Nat -> Nat
mulN n = foldN Zero (addN n)

prop_mulN :: Nat -> Nat -> Bool
prop_mulN n m = mulN n m == toN (fromN n * fromN m)

powN :: Nat -> Nat -> Nat
powN n = foldN (Succ Zero) (mulN n)

prop_powN :: Nat -> Nat -> Property
prop_powN n m = 
    forAll (fmap toN (resize 4 arbitrarySizedNatural)) $ \n ->
        forAll (fmap toN (resize 4 arbitrarySizedNatural)) $ \m ->
            powN n m == toN (fromN n ^ fromN m)

-- exercise 3.19

predN :: Nat -> Maybe Nat
predN Zero = Nothing
predN (Succ n) = Just n

predN' :: Nat -> Maybe Nat
predN' = foldN Nothing (maybe (Just Zero) (Just . Succ))

prop_predN' :: Nat -> Bool
prop_predN' n = predN n == predN' n

-- exercise 3.20

subN :: Nat -> Nat -> Maybe Nat
subN n = foldN (Just n) (>>= predN)

prop_subN :: Nat -> Nat -> Bool
prop_subN n m = subN n m == toN' (fromN n - fromN m)
  where
    toN' n = if n < 0 then Nothing else Just (toN n)

eqN :: Nat -> Nat -> Bool
eqN n m =  (subN n m == Just Zero) && (subN m n == Just Zero)

prop_eqN :: Nat -> Nat -> Bool
prop_eqN n m = eqN n m == (fromN n == fromN m)

lessN :: Nat -> Nat -> Bool
lessN n m = not $ isNothing $ subN m n

prop_lessN :: Nat -> Nat -> Bool
prop_lessN n m = lessN n m == (fromN n <= fromN m)

-- exercise 3.21

takeN :: Int -> Nat -> Nat
takeN _ Zero = Zero
takeN 0 n = Zero
takeN n (Succ m) = Succ (takeN (n-1) m)

unfoldN' :: (a -> Maybe a) -> a -> Nat
unfoldN' f x = case f x of
    Nothing -> Zero
    Just y -> Succ (unfoldN' f y)

myUnfoldN' :: (a -> Maybe a) -> a -> Nat
myUnfoldN' f = unfoldN (isNothing . f) (fromJust . f)

prop_myUnfoldN' :: (Int -> Maybe Int) -> Int -> Bool
prop_myUnfoldN' f x =
    takeN 100 (unfoldN' f x) == takeN 100 (myUnfoldN' f x)

unfoldN :: (a -> Bool) -> (a -> a) -> a -> Nat
unfoldN p f x = if p x then Zero else Succ (unfoldN p f (f x))

myUnfoldN :: (a -> Bool) -> (a -> a) -> a -> Nat
myUnfoldN p f = unfoldN' (\x -> if p x then Nothing else Just (f x))

prop_myUnfoldN :: (Int -> Bool) -> (Int -> Int) -> Int -> Bool
prop_myUnfoldN p f x =
    takeN 100 (unfoldN p f x) == takeN 100 (myUnfoldN p f x)

-- exercise 3.23

divN :: Nat -> Nat -> Nat
divN n m = unfoldN (isNothing . flip subN m) (fromJust . flip subN m) n

prop_divN :: Nat -> Nat -> Property
prop_divN n m =
    forAll (fmap (toN . (+1)) arbitrarySizedNatural) $ \m ->
        divN n m == toN (fromN n `div` fromN m)

-- exercise 3.24

logN :: Nat -> Nat
logN = unfoldN (flip lessN (Succ Zero)) (flip divN (Succ (Succ Zero)))

prop_logN :: Nat -> Property
prop_logN n =
    forAll (fmap (toN . (+1)) arbitrarySizedNatural) $ \n ->
        logN n == toN (floor (logBase 2 (fromIntegral $ fromN n)))

-- exercise 3.25

hyloN' :: (Maybe a -> a) -> (a -> Maybe a) -> a -> a
hyloN' f g = foldN' f . unfoldN' g

myHyloN' :: (Maybe a -> a) -> (a -> Maybe a) -> a -> a
myHyloN' f g = f . fmap (myHyloN' f g) . g

-- prop_myHyloN' :: (Maybe Int -> Int) -> (Int -> Maybe Int) -> Int -> Bool
-- prop_myHyloN' f g n = hyloN' f g n == myHyloN' f g n

hyloL' :: (Maybe (b,c) -> c) -> (a -> Maybe (b,a)) -> a -> c
hyloL' f g = foldL' f . unfoldL' g

-- exercise 3.28

fix :: (a -> a) -> a
fix f = hyloL' (uncurry ($) . fromJust) (const (Just (f, undefined))) f

-- exercise 3.29

data Rose a = Node a (Forest a) deriving (Show, Eq, Functor)
type Forest a = List (Rose a)

instance Arbitrary a => Arbitrary (Rose a) where
    arbitrary = resize 4 (sized arbitrarySizedRose)

arbitrarySizedRose :: Arbitrary a => Int -> Gen (Rose a)
arbitrarySizedRose n =
    Node <$> arbitrary
         <*> (toL <$> resize n (listOf (arbitrarySizedRose (n-1))))

foldR :: (a -> c -> b) -> (List b -> c) -> Rose a -> b
foldR f g (Node a ts) = f a (foldF f g ts)

foldF :: (a -> c -> b) -> (List b -> c) -> Forest a -> c
foldF f g ts = g (mapL (foldR f g) ts)

foldRose :: (a -> List b -> b) -> Rose a -> b
foldRose f (Node a ts) = f a (mapL (foldRose f) ts)

myFoldRose :: (a -> List b -> b) -> Rose a -> b
myFoldRose f = foldR f id

prop_myFoldRose :: (Int -> List Int -> Int) -> Rose Int -> Bool
prop_myFoldRose f t = foldRose f t == myFoldRose f t

myFoldR :: (a -> c -> b) -> (List b -> c) -> Rose a -> b
myFoldR f g = foldRose h
  where
    h x ys = f x (g ys)

prop_myFoldR :: (Int -> Int -> Int) -> (List Int -> Int) -> Rose Int -> Bool
prop_myFoldR f g t = foldR f g t == myFoldR f g t

-- exercise 3.30

-- Universal property
--   k (Node a ts) = f a (g (mapL k ts)) iff k = foldR f g

-- Fusion law
--   h . foldR f g = foldR f' g'
-- ⇔ h (f a (g (mapL (foldR f g) ts))) = f' a (g' (mapL (h . foldR f g) ts))
-- ⇐ h (f x y) = f' x (h y)                                                 (1)
--   ∧ h (g z) = g' (mapL h z)                                              (2)
-- Proof of implication
--   h . foldR f g (Node a ts)
-- = h (f a (g (mapL (foldR f g) ts)))
-- = f' a (h (g (mapL (foldR f g) ts)))                                   [(1)]
-- = f' a (g' (mapL h (mapL (foldR f g) ts)))                             [(2)]
-- = f' a (g' (mapL (h . foldR f g) ts))                                 [mapL]

-- exercise 3.31

dft :: Rose a -> List a
dff :: Forest a -> List a
(dft, dff) = (foldR f g, foldF f g)
  where
    f = Cons
    g = concatL

type DList a = List a -> List a

appD :: DList a -> List a
appD xs = xs Nil

consD :: a -> DList a -> DList a
consD x xs = \ys -> Cons x (xs ys)

concatD :: List (DList a) -> DList a
concatD xss = \ys -> foldL ($) ys xss

myDft :: Rose a -> List a
myDff :: Forest a -> List a
(myDft, myDff) = (appD . foldR consD concatD, appD . foldF consD concatD)

prop_myDft :: Rose Int -> Bool
prop_myDft t = dft t == myDft t

prop_myDff :: Forest Int -> Bool
prop_myDff ts = dff ts == myDff ts

-- Looks like the condition for the fusion law described above is too strict:

-- Condition (1) is satisfied:
--   h (f x y)
-- = ($ Nil) (consD x y)
-- = consD x y Nil
-- = Cons x (y Nil)
-- = Cons x (($ Nil) y)
-- = f' x (h y)

-- But for condition (2):
--   h (g z)
-- = ($ Nil) (concatD z)
-- = concatD z Nil
-- = foldL ($) Nil z
-- ≠ foldL (appendL . ($ Nil)) Nil z                                        (*)
-- = foldL appendL Nil (mapL ($ Nil) z)                                (Ex 3.3)
-- = concatL (mapL ($ Nil) z)
-- = g' (mapL h z)

-- Where (*) is generally an inequality, even though it is an equality for the
-- z we are interested in, so there is probably a version of the fusion law
-- with a weaker condition.

-- exercise 3.32

levelt :: Rose a -> List (List a)
levelf :: Forest a -> List (List a)
(levelt, levelf) = (foldR f g, foldF f g)
  where
    f x xss = Cons (wrap x) xss
    g = foldL (lzw appendL) Nil

lzw :: (a -> a -> a) -> List a -> List a -> List a
lzw f Nil ys = ys
lzw f xs Nil = xs
lzw f (Cons x xs) (Cons y ys) = Cons (f x y) (lzw f xs ys)

myLzw :: (a -> a -> a) -> List a -> List a -> List a
myLzw f xs ys = unfoldL p g h (xs,ys)
  where
    p (Nil,Nil) = True
    p _         = False
    g (Cons x _ , Cons y _ ) = f x y
    g (Cons x _ , Nil      ) = x
    g (Nil      , Cons y _ ) = y
    h (Cons _ xs, Cons _ ys) = (xs,  ys )
    h (Cons _ xs, Nil      ) = (xs,  Nil)
    h (Nil      , Cons _ ys) = (Nil, ys )

prop_myLzw :: (Int -> Int -> Int) -> List Int -> List Int -> Bool
prop_myLzw f xs ys = lzw f xs ys == myLzw f xs ys

-- exercise 3.33

myLzwA :: (a -> a -> a) -> List a -> List a -> List a
myLzwA f xs ys = apoL' g (xs,ys)
  where
    g (Nil      , Nil      ) = Nothing
    g (Cons x xs, Nil      ) = Just (x, Right xs)
    g (Nil      , Cons y ys) = Just (y, Right ys)
    g (Cons x xs, Cons y ys) = Just (f x y, Left (xs,ys))

prop_myLzwA :: (Int -> Int -> Int) -> List Int -> List Int -> Bool
prop_myLzwA f xs ys = lzw f xs ys == myLzwA f xs ys

prop_unk :: List (DList Int) -> Bool
prop_unk xs = foldL ($) Nil xs == foldL (appendL . ($ Nil)) Nil xs

-------------------------------------------------------------------------------

return []
runTests = $quickCheckAll

main :: IO ()
main = runTests >> return ()
