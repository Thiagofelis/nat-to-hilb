module NatToHilb.Examples where
import NatToHilb.NaturalDeduction
import NatToHilb.NatToHilb
import NatToHilb.HilbertSystem
import NatToHilb.Type
import NatToHilb.TypedHilbert

-- ------- some proofs in natural deduction --------

-- proof of (not A \/ B) -> A -> B
test0 = Abs 0 (Abs 1 (Case
                      (Var 0)
                      (Abs 3 (Exfalso
                               (App (Var 3) (Var 1)) ))
                      (Abs 4 (Var 4))))
-- proof of A -> (not A) -> B 
test1 = Abs 0 (Abs 1 (Exfalso (App (Var 1) (Var 0))))
-- A -> B -> A
test2 = Abs 1 (Abs 2 (Var 1))
-- A -> B -> C -> C
test3 = Abs 1 (Abs 2 (Abs 0 (Var 0)))
-- A -> B -> B
test4 = Abs 2 (Abs 0 (Var 0))
-- (A /\ B) -> (B /\ A)
test5 = Abs 0 (Prod (Pi2 (Var 0)) (Pi1 (Var 0)))
-- (False /\ B) -> C
test6 = Abs 0 (Exfalso (Pi1 (Var 0)))
-- (A /\ B) -> (A \/ B)
test7 = Abs 0 (Inl (Pi1 (Var 0)))
-- A -> A
test8 = Abs 3 (Var 3)
-- not a proof
err = Abs 0 (App (Var 0) (Var 0))
-- (A \/ B) -> (B \/ A)
test9 = Abs 0 (Case
               (Var 0)
               (Abs 1 (Inr (Var 1)))
               (Abs 2 (Inl (Var 2))))
-- A -> (A /\ A)
test10 = Abs 0 (Prod (Var 0) (Var 0))

proofs = [test0, test1, test2, test3, test4,
          test5, test6, test7, test8, test9, test10]

-- their translation to the hilbert system 

hproofs = map nattohilb proofs

-- ---- their typed versions -----

htypedproofs = map (\x -> case (annotate x) of Just x -> x) hproofs

-- ------ checks that they are correctly typed ------

htpcheck = map (\x -> typecheck x) htypedproofs

-- gets the type of each proof, that is, the proposition
-- that it proves

htptypes = map (\x -> gettype x) htypedproofs
           
-- obs. note that the type of proof 7 given in the list is
-- (A /\ B) -> (A \/ C), which is different from the one shown
-- before. this happens because the proof of (A /\ B) -> (A \/ B)
-- that we gave can be also typed as a proof of (A /\ B) -> (A \/ C),
-- and this is its most general type. indead, by taking B = C we get
-- the proof that we wanted
