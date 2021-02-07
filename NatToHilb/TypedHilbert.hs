module NatToHilb.TypedHilbert where
import NatToHilb.Type
import NatToHilb.HilbertSystem
import Data.List
import Data.Maybe

-- Hilbert System with annotated proof terms
-- aka SKI calculus with constructors and eliminators
-- for AND, OR and FALSE and typing a la Church 
data TypedHilb = AxT Int Type
               | MPT TypedHilb TypedHilb Type
               | ST Type | KT Type
               | IandT Type | ERandT Type | ELandT Type
               | IRorT Type | ILorT Type  | EorT Type
               | ExFT Type deriving (Eq, Read, Show)

-- (replace a n x) replaces all the occurences of type
-- (Base n) by the type x on the annotations of all
-- subterms of a
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

-- returns the type
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

-- given terms a and b, such that no base type (Base n)
-- occurs in both of a and b, returns (MPT a' b' x) if
-- there exists a type x such that we can type (MP a' b') with x
-- after doing unification on a and b
-- returns Nothing if it is not possible
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


-- (typeinf a n) returns a typed version of a, if it is possible.
-- the fresh base terms are taken to be those starting from n,
-- and this function also return an m st all base types of the
-- typed term are less then m.
-- ! only works for closed terms ! (you can always use abselim to
-- eliminate the axioms before runing this algorithm)
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


typesinterm :: TypedHilb -> [Int]
typesinterm (AxT a x) = basetypes x
typesinterm (MPT a b x) = (typesinterm a) ++ (typesinterm b) ++ (basetypes x)
typesinterm (KT x) = (basetypes x)
typesinterm (ST x) = (basetypes x)
typesinterm (IandT x) = (basetypes x)
typesinterm (ERandT x) = (basetypes x)
typesinterm (ELandT x) = (basetypes x)
typesinterm (IRorT x) = (basetypes x)
typesinterm (ILorT x) = (basetypes x)
typesinterm (EorT x) = (basetypes x)
typesinterm (ExFT x) = (basetypes x)

annotate :: Hilb -> Maybe TypedHilb
annotate a = (typeinf a 0) >>=
             (\x -> let (a', n) = x in
                      let removel = (\y l -> filter (\w -> not (w == y)) l) in
                        let mexl = (\l -> filter (\w -> not (elem w l)) [0,1..(maximum l)]) in
                          let renvar = (\x -> case x of (l, b) ->
                                                          let l' = mexl l in
                                                            if (l' == []) then b else
                                                            let oldn = maximum l in
                                                              let newn = head l' in
                                                                renvar (newn : (removel oldn l), replace b oldn (Base newn))) in
                              Just (renvar (typesinterm a', a')))

typeofhilb :: Hilb -> Maybe Type
typeofhilb a = annotate a >>= (\x -> Just (gettype x))

typecheck :: TypedHilb -> Bool
-- we assume the axiom has the right type. ideally
-- this should be used only with closed terms
typecheck (AxT a x) = True
typecheck (MPT a b x) = case (gettype a) of
                          Arrow t1 t2 -> and [(t1 == gettype b), (t2 == x), typecheck a, typecheck b]
                          _ -> False
typecheck (KT x) = case x of
                     Arrow t1 (Arrow t2 t3) -> (t1 == t3)
                     _ -> False
typecheck (ST x) = case x of
                     (Arrow
                       (Arrow
                         t1
                         (Arrow t2 t3))
                       (Arrow
                         (Arrow t4 t5)
                         (Arrow t6 t7))) -> and [t1 == t4, t2 == t5, t1 == t6, t3 == t7]
                     _ -> False
typecheck (IandT x) = case x of
                        (Arrow
                         t1
                          (Arrow
                           t2
                            (Product t3 t4))) -> and [t1 == t3, t2 == t4]
                        _ -> False
typecheck (ELandT x) = case x of
                         (Arrow
                           (Product t1 t2)
                           t3) -> (t1 == t3)
                         _ -> False
typecheck (ERandT x) = case x of
                         (Arrow
                           (Product t1 t2)
                           t3) -> (t2 == t3)
                         _ -> False
typecheck (ILorT x) = case x of
                         (Arrow
                           t1
                           (Sum t2 t3)) -> (t1 == t2)
                         _ -> False
typecheck (IRorT x) = case x of
                         (Arrow
                           t1
                           (Sum t2 t3)) -> (t1 == t3)
                         _ -> False
typecheck (EorT x) = case x of
                       (Arrow
                         (Sum t1 t2)
                         (Arrow
                           (Arrow t3 t4)
                           (Arrow
                             (Arrow t5 t6)
                             t7))) -> and [t1 == t3, t2 == t5, t4 == t6, t4 == t7]
                       _ -> False
typecheck (ExFT x) = case x of
                       (Arrow Bot t) -> True
                       _ -> False
