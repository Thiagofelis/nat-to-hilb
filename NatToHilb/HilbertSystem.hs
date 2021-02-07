module NatToHilb.HilbertSystem where
import Data.List
import Data.Maybe

-- Hilbert System aka SKI calculus with axioms for AND, OR and FALSE
data Hilb = Ax Int
          | MP Hilb Hilb
          | S | K
          | Iand | ERand | ELand
          | IRor | ILor  | Eor
          | ExF deriving (Eq, Read, Show)

-- (hilbvar a x) returns true if (Ax x) occurs in a
hilbvar :: Hilb -> Int -> Bool
hilbvar (Ax y) x = if (x == y) then True else False
hilbvar (MP a b) x = or [hilbvar a x, hilbvar b x]
hilbvar _ x = False

-- if a is a proof of A with possible occurences of Ax n of type B, then
-- (combabstraction n a) returns a proof of B -> A in which Ax n does not appear.
-- this is the algorithmic content of the proof of the deduction theorem
-- for the Hilbert System
combabstraction :: Int -> Hilb -> Hilb
combabstraction x (Ax y) = if (y == x) then (MP (MP S K) K) else (MP K (Ax y))
combabstraction x (MP a b) = if (hilbvar (MP a b) x)
                             then (MP (MP S (combabstraction x a)) (combabstraction x b))
                             else (MP K (MP a b))
combabstraction x c = MP K c

-- eliminates cuts
hilbred :: Hilb -> Hilb
hilbred (MP x y) = let reda = hilbred x in
                     let redb = hilbred y in
                       case (MP reda redb) of
                         MP (MP K a) b -> hilbred a
                         MP (MP (MP S a) b) c -> hilbred (MP (MP a c) (MP b c))
                         MP ELand (MP (MP Iand a) b) -> hilbred a
                         MP ERand (MP (MP Iand a) b) -> hilbred b
                         MP (MP (MP Eor (MP ILor a)) b) c -> hilbred (MP b a)
                         MP (MP (MP Eor (MP IRor a)) b) c -> hilbred (MP c a)
                         MP a b -> MP a b
hilbred c = c
