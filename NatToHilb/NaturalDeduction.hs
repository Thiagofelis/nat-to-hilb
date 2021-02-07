module NatToHilb.NaturalDeduction where
import Data.List

-- the natural deduction system aka the lambda calculus with
-- sums, products and a bottom type
data NatDed = Var Int
            | App NatDed NatDed | Abs Int NatDed
            | Prod NatDed NatDed | Pi1 NatDed | Pi2 NatDed
            | Inl NatDed | Inr NatDed | Case NatDed NatDed NatDed
            | Exfalso NatDed deriving (Eq, Read, Show)
-- a small modification is that Case (the elimination of OR)
-- takes P1 : (A \/ B), P2 : (A -> C) and P3 : (B -> C) instead of
-- P1 : (A \/ B), P2 : C and P3 : C in which P2 (P3) has a free occurence
-- of a variables of type A (B)

-- (allvar a n) returns true iff (Var n) appears in a in any possbile form,
-- that is, free, bounded or in binder
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

-- (renames a x z) renames free occurences of x into z
-- z is assumed to not occur at all in a
rename :: NatDed -> Int -> Int -> NatDed
rename (Var y) x z = if (x == y) then (Var z) else (Var y)
rename (App a b) x z = App (rename a x z) (rename b x z)
-- if y = x, then x occurs bounded in a, thus we do not rename
rename (Abs y a) x z = if (y == x) then (Abs y a) else Abs y (rename a x z)
rename (Prod a b) x z = Prod (rename a x z) (rename b x z)
rename (Pi1 a) x z = Pi1 (rename a x z)
rename (Pi2 a) x z = Pi2 (rename a x z)
rename (Inl a) x z = Inl (rename a x z)
rename (Inr a) x z = Inr (rename a x z)
rename (Case a b c) x z = Case (rename a x z) (rename b x z) (rename c x z)
rename (Exfalso a) x z = Exfalso (rename a x z)

-- |(freevar a n) is true if (Var n) occurs free in a
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
