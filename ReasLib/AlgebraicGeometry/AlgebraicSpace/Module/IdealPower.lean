/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Ideal-power products of modules on algebraic spaces

The product `I^n G` of a power of a quasi-coherent ideal sheaf with a
subobject of an `𝒪_X`-module is the image of the iterated ideal-sheaf
action. The case `G = ⊤` recovers `I^n F`.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

variable {X}

/-- The canonical action `(I : X.Modules) ⊗ F ⟶ F` induced by the inclusion of an
ideal sheaf into the structure module. -/
noncomputable def action (I : IdealSubobject X) (F : X.Modules) :
    I.toModule ⊗ F ⟶ F :=
  (I.arrow ▷ F) ≫ (structureModuleIsoTensorUnit X).hom ▷ F ≫ (λ_ F).hom

/-- The ideal-sheaf action is whiskering of the inclusion, comparison with the
tensor unit, and the left unitor. -/
theorem action_eq (I : IdealSubobject X) (F : X.Modules) :
    action I F =
      (I.arrow ▷ F) ≫ (structureModuleIsoTensorUnit X).hom ▷ F ≫ (λ_ F).hom :=
  sorry

/-- The image subobject `I^n G` obtained by applying the `n`th power of an ideal
sheaf to a subobject `G` of an `𝒪_X`-module. -/
noncomputable def idealPowerSmulSubobject {F : X.Modules} (I : IdealSubobject X)
    (G : Subobject F) : ℕ → Subobject F :=
  Nat.rec G fun _ stage ↦
    imageSubobject (action I (stage : X.Modules) ≫ stage.arrow)

/-- The zeroth ideal-power product of a subobject is the subobject itself. -/
theorem idealPowerSmulSubobject_zero {F : X.Modules} (I : IdealSubobject X)
    (G : Subobject F) :
    idealPowerSmulSubobject I G 0 = G :=
  sorry

/-- The successor ideal-power product is the image of the ideal-sheaf action on
the previous stage. -/
theorem idealPowerSmulSubobject_succ {F : X.Modules} (I : IdealSubobject X)
    (G : Subobject F) (n : ℕ) :
    idealPowerSmulSubobject I G (n + 1) =
      imageSubobject
        (action I (idealPowerSmulSubobject I G n : X.Modules) ≫
          (idealPowerSmulSubobject I G n).arrow) :=
  sorry

/-- The image subobject `I^n F` obtained by applying the `n`th power of an ideal
sheaf to an `𝒪_X`-module. -/
noncomputable abbrev idealPowerProductSubobject (I : IdealSubobject X)
    (F : X.Modules) (n : ℕ) : Subobject F :=
  idealPowerSmulSubobject I (⊤ : Subobject F) n

/-- `I^n F` is the ideal-power product of the maximal subobject of `F`. -/
theorem idealPowerProductSubobject_eq (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) :
    idealPowerProductSubobject I F n =
      idealPowerSmulSubobject I (⊤ : Subobject F) n :=
  sorry


/-- The image of `I ^ n F` under a module morphism lands in `I ^ n G`. -/
theorem idealPowerProduct_image_le (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    imageSubobject ((idealPowerProductSubobject I F n).arrow ≫ f) ≤
      idealPowerProductSubobject I G n := sorry

/-- A morphism of modules induces a morphism of ideal-power product subobjects. -/
def idealPowerProductHom (I : IdealSubobject X) {F G : X.Modules} (f : F ⟶ G)
    (n : ℕ) :
    (idealPowerProductSubobject I F n : X.Modules) ⟶
      (idealPowerProductSubobject I G n : X.Modules) :=
  factorThruImageSubobject ((idealPowerProductSubobject I F n).arrow ≫ f) ≫
    Subobject.ofLE _ _ (idealPowerProduct_image_le I f n)

/-- The induced map on ideal-power products lies over the original module morphism. -/
theorem idealPowerProductHom_arrow (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    (idealPowerProductSubobject I F n).arrow ≫ f =
      idealPowerProductHom I f n ≫ (idealPowerProductSubobject I G n).arrow := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
