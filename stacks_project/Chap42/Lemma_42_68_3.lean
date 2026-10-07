module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Dimension
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 42.68.3: the determinant space of a finite-length module over a local ring has
dimension at most one over the residue field. -/
@[stacks 02P7]
#check (Module.FiniteLengthDeterminant.rank_le_one :
  ∀ (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M),
    Module.rank (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R M hM) ≤ 1)
