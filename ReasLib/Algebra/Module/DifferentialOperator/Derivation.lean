module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.Algebra.Module.DifferentialOperator.Basic

@[expose] public section

universe u v

namespace LinearMap

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/-- A `ℤ`-linear endomorphism of an `A`-module is a module derivation along `θ` if it
satisfies the corresponding Leibniz rule for the `A`-action. -/
def IsModuleDerivation (D : Module.End ℤ M) (θ : Derivation ℤ A A) : Prop :=
  ∀ a x, D (a • x) = a • D x + θ a • x

/-- The pointwise characterization of a module derivation along a ring derivation. -/
theorem isModuleDerivation_iff (D : Module.End ℤ M) (θ : Derivation ℤ A A) :
    D.IsModuleDerivation θ ↔ ∀ a x, D (a • x) = a • D x + θ a • x := sorry

namespace IsModuleDerivation

/-- A module derivation satisfies its defining Leibniz rule pointwise. -/
theorem leibniz {D : Module.End ℤ M} {θ : Derivation ℤ A A}
    (hD : D.IsModuleDerivation θ) (a : A) (x : M) :
    D (a • x) = a • D x + θ a • x := sorry

/-- A module derivation along a ring derivation is a differential operator of order at most one. -/
theorem orderLEOne {D : Module.End ℤ M} {θ : Derivation ℤ A A}
    (hD : D.IsModuleDerivation θ) :
    D.IsDifferentialOperatorOfOrder A 1 := sorry

end IsModuleDerivation

end LinearMap
