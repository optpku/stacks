module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

universe u v

open scoped TensorProduct

namespace Localization

variable {A : Type u} [CommRing A]

/-- The localization of an `A`-module at `S` is canonically linearly equivalent over
`Localization S` to scalar extension `Localization S ⊗[A] M`. -/
noncomputable def moduleEquivTensorProduct (S : Submonoid A) (M : Type v)
    [AddCommGroup M] [Module A M] :
    LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[A] M :=
  LocalizedModule.equivTensorProduct S M

/-- The localization of a commutative ring at any submonoid is flat as a module
over the original ring. -/
theorem flatModule (S : Submonoid A) : Module.Flat A (Localization S) :=
  IsLocalization.flat (Localization S) S

end Localization
