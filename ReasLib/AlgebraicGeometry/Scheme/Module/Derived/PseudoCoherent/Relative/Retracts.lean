module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative

@[expose] public section

/-!
# Retracts of relatively pseudo-coherent derived scheme modules

Relative fixed-degree pseudo-coherence over a scheme morphism is stable under retracts.
This gives the standard direct-summand interface for biproducts.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- Relative `m`-pseudo-coherence over a locally finite type scheme morphism is stable
under retracts. -/
instance mPseudoCoherentOver_isStableUnderRetracts (f : X ⟶ S)
    [LocallyOfFiniteType f] (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts (mPseudoCoherentOver f m) := sorry

namespace IsMPseudoCoherentOver

/-- Both summands of a relatively `m`-pseudo-coherent biproduct are relatively
`m`-pseudo-coherent. -/
theorem summands (f : X ⟶ S) [LocallyOfFiniteType f]
    (E K : RingedSpace.ModuleDerived X.toRingedSpace) {m : ℤ}
    (hEK : IsMPseudoCoherentOver f (E ⊞ K) m) :
    IsMPseudoCoherentOver f E m ∧ IsMPseudoCoherentOver f K m := sorry

/-- The left summand of a relatively `m`-pseudo-coherent biproduct is relatively
`m`-pseudo-coherent. -/
theorem left (f : X ⟶ S) [LocallyOfFiniteType f]
    (E K : RingedSpace.ModuleDerived X.toRingedSpace) {m : ℤ}
    (hEK : IsMPseudoCoherentOver f (E ⊞ K) m) :
    IsMPseudoCoherentOver f E m := sorry

/-- The right summand of a relatively `m`-pseudo-coherent biproduct is relatively
`m`-pseudo-coherent. -/
theorem right (f : X ⟶ S) [LocallyOfFiniteType f]
    (E K : RingedSpace.ModuleDerived X.toRingedSpace) {m : ℤ}
    (hEK : IsMPseudoCoherentOver f (E ⊞ K) m) :
    IsMPseudoCoherentOver f K m := sorry

end IsMPseudoCoherentOver

end AlgebraicGeometry.Scheme.ModuleDerived
