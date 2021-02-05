import System.Environment
import System.IO
import Data.List


data NatDed = Var Int
            | App NatDed NatDed | Abs Int NatDed
            | Prod NatDed NatDed | Pi1 NatDed | Pi2 NatDed
            | Inl NatDed | Inr NatDed | Case NatDed NatDed NatDed
            | Exfalso NatDed deriving (Eq,Read, Show)

data Hilb = Ax Int
          | MP Hilb Hilb
          | S | K
          | Iand | ERand | ELand
          | IRor | ILor  | Eor
          | ExF deriving (Eq,Read, Show)

allvar :: NatDed -> Int -> Bool
allvar (Var y) x = if (x == y) then True else False
allvar (App a b) x = or [allvar a x, allvar b x]
allvar (Abs y a) x = if (x == y) then True else (allvar a x)
allvar (Prod a b) x = or [allvar a x, allvar b x]
allvar (Pi1 a) x = allvar a x
allvar (Pi2 a) x = allvar a x
allvar (Inl a) x = allvar a x
allvar (Inr a) x = allvar a x
allvar (Case a b c) x = or [allvar a x, allvar b x, allvar c x]
allvar (Exfalso a) x = allvar a x

rename :: NatDed -> Int -> Int -> NatDed
-- renames free occurences of x into z, which is assumed to not occur at all
rename (Var y) x z = if (x == y) then (Var z) else (Var y)
rename (App a b) x z = App (rename a x z) (rename b x z)
rename (Abs y a) x z = if (y == x) then (Abs y a) else Abs y (rename a x z)
-- assumes that z does not occur at all
-- if y = x, then it occurs bounded in a, thus we do not rename
rename (Prod a b) x z = Prod (rename a x z) (rename b x z)
rename (Pi1 a) x z = Pi1 (rename a x z)
rename (Pi2 a) x z = Pi2 (rename a x z)
rename (Inl a) x z = Inl (rename a x z)
rename (Inr a) x z = Inr (rename a x z)
rename (Case a b c) x z = Case (rename a x z) (rename b x z) (rename c x z)
rename (Exfalso a) x z = Exfalso (rename a x z)

freevar :: NatDed -> Int -> Bool
freevar (Var y) x = if (x == y) then True else False
freevar (App a b) x = or [freevar a x, freevar b x]
freevar (Abs y a) x = if (x == y)
              then let z = (head $ filter (\w -> not (allvar a w)) [0,1..])
                       in (freevar (rename a y z) x)
              else (freevar a x)
freevar (Prod a b) x = or [freevar a x, freevar b x]
freevar (Pi1 a) x = freevar a x
freevar (Pi2 a) x = freevar a x
freevar (Inl a) x = freevar a x
freevar (Inr a) x = freevar a x
freevar (Case a b c) x = or [freevar a x, freevar b x, freevar c x]
freevar (Exfalso a) x = freevar a x

hilbfv :: Hilb -> Int -> Bool
hilbfv (Ax y) x = if (x == y) then True else False
hilbfv (MP a b) x = or [hilbfv a x, hilbfv b x]
hilbfv _ x = False

abselim :: Int -> Hilb -> Hilb
abselim x (Ax y) = if (y == x) then (MP (MP S K) K) else (MP K (Ax y))
abselim x (MP a b) = if (hilbfv (MP a b) x) then (MP (MP S (abselim x a)) (abselim x b)) else (MP K (MP a b))
-- "lazy" translation, terms are much bigger while stying being irreducible
--abselim x (MP a b) = MP (MP S (abselim x a)) (abselim x b)
abselim x c = MP K c



nattohilb :: NatDed -> Hilb
nattohilb (Var x) = Ax x
nattohilb (App a b) = MP (nattohilb a) (nattohilb b)
nattohilb (Abs y a) = abselim y (nattohilb a)
nattohilb (Prod a b) = MP (MP Iand (nattohilb a)) (nattohilb b)
nattohilb (Pi1 a) = MP ELand (nattohilb a)
nattohilb (Pi2 a) = MP ERand (nattohilb a)
nattohilb (Inl a) = MP ILor (nattohilb a)
nattohilb (Inr a) = MP IRor (nattohilb a)
nattohilb (Case a b c) = MP (MP (MP Eor (nattohilb a)) (nattohilb b)) (nattohilb c)
nattohilb (Exfalso a) = MP ExF (nattohilb a)

red :: Hilb -> Hilb
red (MP x y) = let reda = red x in
                 let redb = red y in
                   case (MP reda redb) of
                     MP (MP K a) b -> red a
                     MP (MP (MP S a) b) c -> red (MP (MP a c) (MP b c))
                     MP ELand (MP (MP Iand a) b) -> red a
                     MP ERand (MP (MP Iand a) b) -> red b
                     MP (MP (MP Eor (MP ILor a)) b) c -> red (MP b a)
                     MP (MP (MP Eor (MP IRor a)) b) c -> red (MP c a)
                     MP a b -> MP a b
red c = c


-- proof of (not A \/ B) -> A -> B
test = Abs 0 (Abs 1 (Case (Var 0) (Exfalso (App (Var 0) (Var 1))) (Var 0)))
-- A -> B -> A
test2 = Abs 1 (Abs 2 (Var 1))
-- A -> B -> C -> C
test3 = Abs 1 (Abs 2 (Abs 0 (Var 0)))
-- A -> B -> B
test4 = Abs 2 (Abs 0 (Var 0))
-- (A /\ B) -> (B /\ A)
abba = Abs 0 (Prod (Pi2 (Var 0)) (Pi1 (Var 0)))
-- (False /\ B) -> C
test5 = Abs 0 (Exfalso (Pi1 (Var 0)))



       
