/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.ExteriorPower
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant

variable (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/- Lemma 42.68.4: for a finite-length module annihilated by the maximal ideal, the
determinant-symbol map to the top exterior power over the residue field is an isomorphism. -/
@[stacks 02P8] #check (Module.FiniteLengthDeterminant.toExteriorPower_bijective R M :
  ∀ (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)),
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    Function.Bijective
      (toExteriorPower R M hM hAnn (length_eq_finrank R M hM hAnn)))

end Module.FiniteLengthDeterminant
