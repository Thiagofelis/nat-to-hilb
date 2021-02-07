module NatToHilb.NatToHilb where
import NatToHilb.HilbertSystem
import NatToHilb.NaturalDeduction

-- translates a proof in natural deduction to a proof in the hilbert system
-- this is the algorithmic contect of the proof that if Gamma |- P in
-- natural deduction then Gamma |- P in the hilbert system
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


