module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Trivial group-ring modules via augmentation

This leaf owns the augmentation `Λ[Γ] →+* Λ` and the trivial `Λ[Γ]`-module `Λ`.
-/

@[expose] public section

open scoped MonoidAlgebra

noncomputable section

universe u w

namespace MonoidAlgebra

variable (Λ : Type u) (Γ : Type w) [Ring Λ] [Monoid Γ]

/-- The augmentation `Λ[Γ] →+* Λ`, as the lift of `RingHom.id Λ` along the
trivial monoid map `Γ →* Λ`. -/
def augmentation : Λ[Γ] →+* Λ :=
  liftNCRingHom (RingHom.id Λ) (1 : Γ →* Λ) fun x _ ↦ Commute.one_right x

/-- The augmentation sends a basis term `single γ r` to the coefficient `r`. -/
theorem augmentation_single (γ : Γ) (r : Λ) :
    augmentation Λ Γ (single γ r) = r :=
  sorry

/-- The `Λ[Γ]`-action on `Λ` through the augmentation. -/
instance instModule_augmentation : Module (Λ[Γ]) Λ :=
  Module.compHom Λ (augmentation Λ Γ)

/-- The trivial `Λ[Γ]`-module `Λ`, obtained by viewing `Λ` as a module through
`augmentation`. -/
abbrev trivialModule : ModuleCat.{u} (Λ[Γ]) :=
  ModuleCat.of (Λ[Γ]) Λ

/-- The coefficient ring `Λ` is a `Λ`-module on the trivial `Λ[Γ]`-module. -/
instance instModuleΛ_trivialModule : Module Λ (trivialModule Λ Γ) :=
  inferInstanceAs (Module Λ Λ)

/-- On the trivial `Λ[Γ]`-module, every group-ring basis element acts as the
identity. -/
theorem trivialModule_spec (γ : Γ) (x : trivialModule Λ Γ) :
    (single γ (1 : Λ) : Λ[Γ]) • x = x :=
  sorry

end MonoidAlgebra
