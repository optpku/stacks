module

public import ReasLib.Algebra.Module.DifferentialOperator.Derivation

@[expose] public section

universe u v

namespace LinearMap

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/- A `ℤ`-linear endomorphism of an `A`-module is a module derivation along `θ` if it
satisfies the corresponding Leibniz rule for the `A`-action. -/
#check (LinearMap.IsModuleDerivation : Module.End ℤ M → Derivation ℤ A A → Prop)

/- The pointwise characterization of a module derivation along a ring derivation. -/
#check (LinearMap.isModuleDerivation_iff :
  ∀ (D : Module.End ℤ M) (θ : Derivation ℤ A A),
    D.IsModuleDerivation θ ↔ ∀ a x, D (a • x) = a • D x + θ a • x)

namespace IsModuleDerivation

/- A module derivation satisfies its defining Leibniz rule pointwise. -/
#check (LinearMap.IsModuleDerivation.leibniz :
  ∀ {D : Module.End ℤ M} {θ : Derivation ℤ A A},
    D.IsModuleDerivation θ → ∀ (a : A) (x : M),
      D (a • x) = a • D x + θ a • x)

/- A module derivation along a ring derivation is a differential operator of order at most one. -/
#check (LinearMap.IsModuleDerivation.orderLEOne :
  ∀ {D : Module.End ℤ M} {θ : Derivation ℤ A A},
    D.IsModuleDerivation θ → D.IsDifferentialOperatorOfOrder A 1)

end IsModuleDerivation

end LinearMap
