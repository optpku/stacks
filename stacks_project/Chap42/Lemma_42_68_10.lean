module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.UnitAction
import StacksCheckRecall

@[expose] public section

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 42.68.10: multiplication by a unit on a finite-length module acts on its
determinant line by the corresponding residue unit raised to the module's length. -/
@[stacks 02PD] #check (Module.FiniteLengthDeterminant.mapEquiv_smulOfUnit :
  ∀ (hM : IsFiniteLength R M) (u : Rˣ),
    mapEquiv hM hM (LinearEquiv.smulOfUnit u) =
      LinearEquiv.smulOfUnit
        ((Units.map (IsLocalRing.residue R).toMonoidHom u) ^ length R M hM))

end Module.FiniteLengthDeterminant
