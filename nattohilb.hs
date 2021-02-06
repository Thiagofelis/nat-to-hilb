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

data TypedHilb = AxT Int Type
               | MPT TypedHilb TypedHilb Type
               | ST Type | KT Type
               | IandT Type | ERandT Type | ELandT Type
               | IRorT Type | ILorT Type  | EorT Type
               | ExFT Type deriving (Eq, Read, Show)

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

appearsin :: Type -> Int -> Bool
appearsin (Base n) m = (n == m)
appearsin (Arrow x y) m = or [appearsin x m, appearsin y m]
appearsin (Product x y) m = or [appearsin x m, appearsin y m]
appearsin (Sum x y) m = or [appearsin x m, appearsin y m]
appearsin Bot m = False

subs :: Type -> Int -> Type -> Type
subs (Base n) m y = if (n == m) then y else (Base n)
subs (Arrow x1 x2) m y = Arrow (subs x1 m y) (subs x2 m y)
subs (Product x1 x2) m y = Product (subs x1 m y) (subs x2 m y)
subs (Sum x1 x2) m y = Sum (subs x1 m y) (subs x2 m y)
subs Bot m y = Bot


unify :: [(Type, Type)] -> [(Type, Type)] -> Maybe [(Type, Type)]
unify l1 ((Base n, x) : l2) = if (appearsin x n) then
                                Nothing
                              else
                                let mapsubs = (map (\w -> let (w1, w2) = w in (subs w1 n x, subs w2 n x))) in
                                  let appearsinlist = (\lx -> or $ map (\w -> let (w1, w2) = w in or [appearsin w1 n, appearsin w2 n]) lx) in
                                    if (not $ appearsinlist l1) then
                                      unify ((Base n, x) : l1) (mapsubs l2)
                                    else
                                      unify [] ((mapsubs l1) ++ [(Base n, x)] ++ (mapsubs l2))
unify l1 ((x, Base n) : l2) = unify l1 ((Base n, x) : l2)
unify l1 (((Arrow x1 x2), y) : l2) = case y of
                                       Arrow y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                       _ -> Nothing
unify l1 (((Product x1 x2), y) : l2) = case y of
                                         Product y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                         _ -> Nothing
unify l1 (((Sum x1 x2), y) : l2) = case y of
                                     Sum y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                     _ -> Nothing
unify l1 ((Bot, y) : l2) = case y of
                             Bot -> unify l1 l2
                             _ -> Nothing
unify l1 [] = Just l1 -- end condition


replace :: TypedHilb -> Int -> Type -> TypedHilb
replace (AxT m x) n y = AxT m (subs x n y)
replace (ST x) n y = ST (subs x n y)
replace (KT x) n y = KT (subs x n y)
replace (IandT x) n y = IandT (subs x n y)
replace (ERandT x) n y = ERandT (subs x n y)
replace (ELandT x) n y = ELandT (subs x n y)
replace (IRorT x) n y = IRorT (subs x n y)
replace (ILorT x) n y = ILorT (subs x n y)
replace (EorT x) n y = EorT (subs x n y)
replace (ExFT x) n y = ExFT (subs x n y)
replace (MPT a b x) n y = MPT (replace a n y) (replace b n y) (subs x n y)

gettype :: TypedHilb -> Type
gettype (AxT m x) = x
gettype (ST x) = x
gettype (KT x) = x
gettype (IandT x) = x
gettype (ERandT x) = x
gettype (ELandT x) = x
gettype (IRorT x) = x
gettype (ILorT x) = x
gettype (EorT x) = x
gettype (ExFT x) = x
gettype (MPT a b x) = x


matchholes :: TypedHilb -> TypedHilb -> Maybe TypedHilb
matchholes a b = let ta = gettype a in
                     case ta of
                       Base n -> let tb = gettype b in         
                                   let nt = Arrow tb (Base n) in
                                     let na = replace a n nt in
                                       Just (MPT na b (Base n))
                       Arrow t1 t2 -> let tb = gettype b in  
                                        let ntb = unify [] [(t1, tb)] in
                                          ntb >>= (\x ->
                                                     let na = (foldl
                                                               (\y w -> let (w1, w2) = w in case w1 of Base k -> replace y k w2)
                                                               a x) in
                                                       let nb = (foldl
                                                                 (\y w -> let (w1, w2) = w in case w1 of Base k -> replace y k w2)
                                                                 b x) in
                                                         let nt = case (gettype na) of Arrow t3 t4 -> t4 in
                                                           Just (MPT na nb nt))
                       _ -> Nothing
                                     

typeinf :: Hilb -> Int -> Maybe (TypedHilb, Int)
typeinf (Ax x) n = Nothing -- we reject open terms
typeinf K n = Just (KT (Arrow
                        (Base n)
                        (Arrow
                          (Base (n + 1))
                          (Base n))),                         
                     n + 2)
typeinf S n = Just (ST (Arrow
                         (Arrow
                           (Base n)
                           (Arrow
                             (Base (n + 1))
                             (Base (n + 2))))
                         (Arrow
                           (Arrow
                             (Base n)
                             (Base (n + 1)))
                           (Arrow
                             (Base n)
                             (Base (n + 2))))),
                     n + 3)
typeinf Iand n = Just (IandT (Arrow
                               (Base n)
                               (Arrow
                                 (Base (n + 1))
                                 (Product
                                   (Base n)
                                   (Base (n + 1))))),
                        n + 2)                                 
typeinf ERand n = Just (ERandT (Arrow
                                 (Product (Base n) (Base (n + 1)))
                                 (Base (n + 1))),
                         n + 2)
typeinf ELand n = Just (ELandT (Arrow
                                 (Product (Base n) (Base (n + 1)))
                                 (Base n)),
                         n + 2)
typeinf IRor n = Just (IRorT (Arrow
                               (Base (n + 1))
                               (Sum (Base n) (Base (n + 1)))),
                        n + 2)
typeinf ILor n = Just (ILorT (Arrow
                               (Base n)
                               (Sum (Base n) (Base (n + 1)))),
                        n + 2)
typeinf Eor n = Just (EorT (Arrow
                             (Sum (Base n) (Base (n + 1)))
                             (Arrow
                               (Arrow (Base n) (Base (n + 2)))
                               (Arrow
                                 (Arrow (Base (n + 1)) (Base (n + 2)))
                                 (Base (n + 2))))),
                       n + 3)
typeinf ExF n = Just (ExFT (Arrow (Bot) (Base n)), n + 1)                             
typeinf (MP a b) n = do
  resa <- typeinf a n
  let (ta, na) = resa
  resb <- typeinf b na
  let (tb, nb) = resb
  nt <- matchholes ta tb
  return (nt, nb)


-- proof of (not A \/ B) -> A -> B
test = Abs 0 (Abs 1 (Case
                      (Var 0)
                      (Abs 3 (Exfalso
                               (App (Var 3) (Var 1)) ))
                      (Abs 4 (Var 4))))
-- proof of A -> ( (not A) -> B )
test1 = Abs 0 (Abs 1 (Exfalso (App (Var 1) (Var 0))))
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
-- (A /\ B) -> (A \/ B)
test6 = Abs 0 (Inl (Pi1 (Var 0)))
-- A -> A
test7 = Abs 3 (Var 3)

err = Abs 0 (App (Var 0) (Var 0))

       
