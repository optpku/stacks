module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

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

/-- The structure-module value of `X` at an étale object. -/
abbrev structureModuleSection (U : (smallEtaleSite X)ᵒᵖ) :=
  (SheafOfModules.unit (structureSheaf X)).val.obj U

/-- The restricted commutative structure-module value of `X` at an étale object. -/
abbrev restrictCommUnitSection (U : (smallEtaleSite X)ᵒᵖ) :=
  ((ofCommModules X).obj
      (unitModule (smallEtaleTopology X) (commStructureSheaf X))).val.obj U

/-- The component of the structure-module comparison at an étale object. -/
noncomputable def structureModuleIsoRestrictCommUnitApp (U : (smallEtaleSite X)ᵒᵖ) :
    structureModuleSection X U ⟶ restrictCommUnitSection X U :=
  ModuleCat.ofHom
    (X := structureModuleSection X U)
    (Y := restrictCommUnitSection X U)
    { toFun := ((commRingSheafIso X).inv.hom.app U).hom
      map_add' := sorry
      map_smul' := sorry }

/-- The inverse component of the structure-module comparison at an étale object. -/
noncomputable def structureModuleIsoRestrictCommUnitAppInv (U : (smallEtaleSite X)ᵒᵖ) :
    restrictCommUnitSection X U ⟶ structureModuleSection X U :=
  ModuleCat.ofHom
    (X := restrictCommUnitSection X U)
    (Y := structureModuleSection X U)
    { toFun := ((commRingSheafIso X).hom.hom.app U).hom
      map_add' := sorry
      map_smul' := sorry }

/-- The structure module of `X` as restriction of scalars of the commutative
structure module along `commRingSheafIso`. -/
noncomputable def structureModuleIsoRestrictCommUnit :
    SheafOfModules.unit (structureSheaf X) ≅
      (ofCommModules X).obj
        (unitModule (smallEtaleTopology X) (commStructureSheaf X)) where
  hom :=
    { val :=
        { app := fun U ↦ structureModuleIsoRestrictCommUnitApp X U
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun U ↦ structureModuleIsoRestrictCommUnitAppInv X U
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The structure module of an algebraic space is canonically isomorphic to the
tensor unit of `X.Modules`. -/
noncomputable def structureModuleIsoTensorUnit :
    SheafOfModules.unit (structureSheaf X) ≅ 𝟙_ X.Modules :=
  structureModuleIsoRestrictCommUnit X ≪≫
    (ofCommModules X).mapIso unitIsoTensorUnit.{u + 1, u, u}

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

end AlgebraicGeometry.AlgebraicSpace.Modules
