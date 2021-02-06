import System.Environment
import System.IO
import Data.List
import Data.Maybe


data NatDed = Var Int
            | App NatDed NatDed | Abs Int NatDed
            | Prod NatDed NatDed | Pi1 NatDed | Pi2 NatDed
            | Inl NatDed | Inr NatDed | Case NatDed NatDed NatDed
            | Exfalso NatDed deriving (Eq, Read, Show)

data Hilb = Ax Int
          | MP Hilb Hilb
          | S | K
          | Iand | ERand | ELand
          | IRor | ILor  | Eor
          | ExF deriving (Eq, Read, Show)

data Type = Base Int
          | Arrow Type Type
          | Product Type Type
          | Sum Type Type
          | Bot deriving (Eq, Read, Show)

data HollowType = Hole Int
                | ArrowH HollowType HollowType
                | ProductH HollowType HollowType
                | SumH HollowType HollowType
                | BotH deriving (Eq, Read, Show)
                

data HollowHilb = AxH Int HollowType
          | MPH HollowHilb HollowHilb HollowType
          | SH HollowType | KH HollowType
          | IandH HollowType | ERandH HollowType | ELandH HollowType
          | IRorH HollowType | ILorH HollowType  | EorH HollowType
          | ExFH HollowType deriving (Eq, Read, Show)

data TypedHilb = AxT Int Type
               | MPT TypedHilb TypedHilb Type
               | ST Type | KT Type
               | IandT Type | ERandT Type | ELandT Type
               | IRorT Type | ILorT Type  | EorT Type
               | ExFT Type deriving (Eq, Read, Show)


--data Ctx = Empty
--         | Cons Type Int

type Ctx = Hilb -> Maybe Type

--data UniEq = Null
--           | Cons Type Type UniEq

data UnifyList = Nil
               | Cons HollowType HollowType UnifyList

          

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

appearsin :: HollowType -> Int -> Bool
appearsin (Hole n) m = (n == m)
appearsin (ArrowH x y) m = or [appearsin x m, appearsin y m]
appearsin (ProductH x y) m = or [appearsin x m, appearsin y m]
appearsin (SumH x y) m = or [appearsin x m, appearsin y m]
appearsin BotH m = False

subs :: HollowType -> Int -> HollowType -> HollowType
subs (Hole n) m y = If (n == m) then y else (Hole n)
subs (ArrowH x1 x2) m y = ArrowH (subs x1 m y) (subs x2 m y)
subs (ProductH x1 x2) m y = ProductH (subs x1 m y) (subs x2 m y)
subs (SumH x1 x2) m y = SumH (subs x1 m y) (subs x2 m y)
subs BotH m y = BotH

unify :: [(HollowType, HollowType)] -> [(HollowType, HollowType)] -> Maybe [(HollowType, HollowType)]
unify l1 ((x, Hole n) : l2) = unify l1 ((Hole n, x) : l2)
unify l1 (((ArrowH x1 x2), y) : l2) = case y of
                                        ArrowH y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                        _ -> Nothing
unify l1 (((ProductH x1 x2), y) : l2) = case y of
                                          ProductH y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                          _ -> Nothing
unify l1 (((SumH x1 x2), y) : l2) = case y of
                                      SumH y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                      _ -> Nothing
unify l1 ((BotH, y) : l2) = case x of
                              BotH -> unify l1 l2
                              _ -> Nothing
unify l1 ((Hole n, x) : l2) = if (appearsin x n) then
                                Nothing
                              else
                                let mapsubs = (map (\w -> let (w1, w2) = w in (subs w1 n x, subs w2 n x))) in
                                  let appearsinlist = (\lx -> or $ map (\w -> let (w1, w2) = w in or [appearsin w1 n, appearsin w2 n]) lx) in
                                    if (not $ appearsinlist l1) then
                                      unify ((Hole n, x) : l1) (mapsubs l2)
                                    else
                                      unify [] ((mapsubs l1) ++ (Hole n, x) ++ (mapsubs l2))
unify l1 [] = Just l1 -- end condition


typeinf :: Hilb -> Int -> Maybe (HollowHilb, Int)
typeinf (Ax x) f n = Nothing -- we reject open terms
typeinf K f n = Just (KH (ArrowH
                         (Hole n)
                         (ArrowH
                           (Hole (n + 1))
                           (Hole n))),                         
                     n + 2)
--typeinf S f = (SH (ArrowH (
typeinf Iand f n = Just (IandH (ArrowH
                               (Hole n)
                               (ArrowH
                                (Hole (n + 1))
                                (ProductH
                                 (Hole n)
                                 (Hole (n + 1))))),
                        n + 2)
typeinf (MP a b) f n = do
  resa <- typeinf a f n
  let (ta,na) = resa
  resb <- typeinf b f na
  let (tb, nb) = resb
  return (matchholes ta tb, nb)
  

--typeinf (MP a b) f n = let (ta, m) = typeinf a f n in
--                        let (tb, o) = typeinf b f m in
--  a                        case ta of
--                            _ 


--putbases :: Hilb -> Int -> (HilbAnnotated, Int)
--putbases (Ax x) n = (AxT x (Base n), n + 1)
--putbases (MP a b) n = let (ta, m) = putbases a n in
--                        let (tb, o) = putbases b m in
--                          (MPT ta tb (Base o), o + 1)
--putbases c n = case c of
--                 K -> (KT (Base n) (Base (n + 1)), n + 2)
--                 S -> (ST (Base n) (Base (n + 1)) (Base (n + 2)), n + 3)
--                 Iand -> (IandT (Base n) (Base (n + 1)), n + 2)
--                 ELand -> (ELandT (Base n) (Base (n + 1)), n + 2)
--                 ERand -> (ERandT (Base n) (Base (n + 1)), n + 2)
--                 Eor -> (EorT (Base n) (Base (n + 1)) (Base (n + 2)), n + 3)
--                 ILor -> (ILorT (Base n) (Base (n + 1)), n + 1)
--                 IRor -> (IRorT (Base n) (Base (n + 1)), n + 1)
--                 ExF -> (ExFT (Base n), n + 1)


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



       
