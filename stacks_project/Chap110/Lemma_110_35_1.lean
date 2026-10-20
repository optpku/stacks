module

public import ReasLib.RingTheory.LocalRing.ZeroDimensionalFlatIdeal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.35.1: there exists a local ring with a unique prime ideal and a
nonzero proper ideal which is a flat module over the ring. -/
@[stacks 05G0] #check (exists_isLocalRing_uniquePrime_nonzero_flat_ideal :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (I : Ideal R),
      (∃! p : Ideal R, p.IsPrime) ∧ I ≠ ⊥ ∧ I ≠ ⊤ ∧ Module.Flat R I)
