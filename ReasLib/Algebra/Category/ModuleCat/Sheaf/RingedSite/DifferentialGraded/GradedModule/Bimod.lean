/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.GradedMonoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule
public import ReasLib.CategoryTheory.GradedObject.Monoidal.Colimit
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded modules as bimodule objects

The tensor-morphism presentation of a graded right module is canonically a bimodule from the
tensor-unit monoid to the underlying graded monoid of its algebra.  This bridge supplies the real
balanced tensor functor used to define relative graded flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

-- Local declaration justification (parser conflict): these lexical aliases keep bimodule formulas
-- readable without adding public notation beside the established graded-module `Mod(...)` scope.
local notation "ModO" => DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := 𝒪)
local notation "GrdO" => GradedObject ℤ ModO

namespace DifferentialGradedAlgebra.GradedModule

/-- Assemble a graded right-module action into a morphism of graded objects. -/
noncomputable def actionHom {A : DGA(𝒪)} (M : GradedModule A) :
    M.toGradedObject ⊗ A.toGradedObject ⟶ M.toGradedObject :=
  CategoryTheory.GradedObject.Monoidal.actionHom
    M.toGradedObject A.toGradedObject M.smul

/-- A graded right module as a bimodule over the tensor-unit monoid and its underlying graded
algebra. -/
@[stacks 0FSA "graded right module as a bimodule object"]
noncomputable def toBimod {A : DGA(𝒪)} (M : GradedModule A) :
    CategoryTheory.Bimod.RightModule A.toGradedMon where
  X := M.toGradedObject
  actLeft := (λ_ M.toGradedObject).hom
  actRight := actionHom M
  one_actLeft := by dsimp [Mon.trivial]; simp
  left_assoc := by dsimp [Mon.trivial]; simp
  actRight_one := by
    apply (cancel_epi (ρ_ M.toGradedObject).inv).1
    funext n
    change (CategoryTheory.GradedObject.Monoidal.rightUnitor M.toGradedObject).inv n ≫
        (CategoryTheory.GradedObject.Monoidal.tensorHom (𝟙 M.toGradedObject)
          (gradedOneHom A)) n ≫ actionHom M n = _
    rw [CategoryTheory.GradedObject.Monoidal.rightUnitor_inv_apply]
    simp only [Category.assoc, CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc,
      CategoryTheory.GradedObject.categoryOfGradedObjects_id]
    simp only [actionHom, CategoryTheory.GradedObject.Monoidal.actionHom,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc]
    have hOne : gradedOneHom A 0 =
        CategoryTheory.GradedObject.Monoidal.tensorUnit₀.hom ≫ A.one := by
      simp [gradedOneHom, CategoryTheory.GradedObject.Monoidal.oneHom,
        CategoryTheory.GradedObject.Monoidal.tensorUnit₀]
    rw [hOne, id_tensorHom, ← whiskerLeft_comp_assoc]
    simp only [Iso.inv_hom_id_assoc]
    rw [← M.one_smul n]
    simp
  right_assoc := by
    change CategoryTheory.GradedObject.Monoidal.tensorHom
        (𝟙 M.toGradedObject) (gradedMulHom A) ≫ actionHom M =
      (CategoryTheory.GradedObject.Monoidal.associator
        M.toGradedObject A.toGradedObject A.toGradedObject).inv ≫
        CategoryTheory.GradedObject.Monoidal.tensorHom (actionHom M)
          (𝟙 A.toGradedObject) ≫ actionHom M
    funext n
    apply CategoryTheory.GradedObject.Monoidal.tensorObj₃_ext
    intro i j k h
    change CategoryTheory.GradedObject.Monoidal.ιTensorObj₃
        M.toGradedObject A.toGradedObject A.toGradedObject i j k n h ≫
        (CategoryTheory.GradedObject.Monoidal.tensorHom
          (𝟙 M.toGradedObject) (gradedMulHom A)) n ≫ actionHom M n = _
    simp only [CategoryTheory.GradedObject.categoryOfGradedObjects_comp]
    rw [CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc]
    dsimp only [CategoryTheory.GradedObject.Monoidal.ιTensorObj₃,
      CategoryTheory.GradedObject.Monoidal.ιTensorObj₃']
    simp only [Category.assoc, CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc,
      CategoryTheory.GradedObject.categoryOfGradedObjects_id,
      id_tensorHom, tensorHom_id]
    rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
    simp only [actionHom, gradedMulHom, CategoryTheory.GradedObject.Monoidal.actionHom,
      CategoryTheory.GradedObject.Monoidal.mulHom,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc,
      eqToHom_refl, Category.comp_id]
    rw [← cancel_epi (α_ (M.obj i) (A.toComplex.X j) (A.toComplex.X k)).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [reassoc_of% (M.smul_assoc i j k)]
    simp
  middle_assoc := by
    change (λ_ M.toGradedObject).hom ▷ A.toGradedObject ≫ actionHom M =
      (α_ (𝟙_ GrdO) M.toGradedObject A.toGradedObject).hom ≫
        (𝟙_ GrdO) ◁ actionHom M ≫ (λ_ M.toGradedObject).hom
    rw [leftUnitor_whiskerRight_assoc, leftUnitor_naturality]

/-- A graded-module map as a morphism of the associated bimodule objects. -/
noncomputable def toBimodMap {A : DGA(𝒪)} {M N : GradedModule A} (f : M ⟶ N) :
    toBimod M ⟶ toBimod N where
  hom := f.hom
  left_act_hom := by
    exact (CategoryTheory.GradedObject.Monoidal.leftUnitor_naturality f.hom).symm
  right_act_hom := by
    change actionHom M ≫ f.hom =
      CategoryTheory.GradedObject.Monoidal.tensorHom f.hom (𝟙 A.toGradedObject) ≫
        actionHom N
    funext n
    apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
    intro i j h
    subst n
    simp only [CategoryTheory.GradedObject.categoryOfGradedObjects_comp,
      CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc,
      CategoryTheory.GradedObject.categoryOfGradedObjects_id, tensorHom_id,
      actionHom, CategoryTheory.GradedObject.Monoidal.actionHom,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc, eqToHom_refl,
      Category.comp_id]
    exact f.comm i j

/-- The canonical functor from graded right modules to bimodule objects. -/
@[stacks 0FSA "graded right module bimodule functor"]
noncomputable def toBimodFunctor (A : DGA(𝒪)) :
    GradedModule A ⥤ CategoryTheory.Bimod.RightModule A.toGradedMon where
  obj := toBimod
  map := toBimodMap
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The carrier of the associated bimodule is the original graded object. -/
@[simp]
theorem toBimod_X {A : DGA(𝒪)} (M : GradedModule A) :
    (toBimod M).X = M.obj := rfl

/-- The right action of the associated bimodule is the assembled graded action. -/
@[simp]
theorem toBimod_actRight {A : DGA(𝒪)} (M : GradedModule A) :
    (toBimod M).actRight = actionHom M := rfl

/-- The bimodule bridge sends a graded-module map to its degreewise underlying map. -/
@[simp]
theorem toBimodMap_hom {A : DGA(𝒪)} {M N : GradedModule A} (f : M ⟶ N) :
    (toBimodMap f).hom = f.hom := rfl

end DifferentialGradedAlgebra.GradedModule

namespace DifferentialGradedAlgebra

/-- Left modules over the underlying graded algebra of `A`. -/
@[stacks 0FSA "left graded module category"]
abbrev LeftGradedModule (A : DGA(𝒪)) :=
  CategoryTheory.Bimod.LeftModule A.toGradedMon

/-- Scoped notation for left modules over an underlying graded algebra. -/
scoped[SheafOfModules.RingedSite.LeftGradedModule] notation:max
    "LGrMod(" A:arg ")" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra.LeftGradedModule A

end DifferentialGradedAlgebra

open scoped SheafOfModules.RingedSite.LeftGradedModule

namespace DifferentialGradedAlgebra.GradedModule

/-- Tensoring a fixed graded right `A`-module with graded left `A`-modules. -/
@[stacks 0FSA "relative graded tensor functor"]
noncomputable def tensorFunctor {A : DGA(𝒪)} (M : GradedModule A) :
    LGrMod(A) ⥤ GrdO :=
  CategoryTheory.Bimod.tensorFunctor (toBimod M)

/-- The relative tensor product of a graded right and a graded left `A`-module. -/
@[stacks 0FSA "relative graded tensor product"]
noncomputable abbrev tensor {A : DGA(𝒪)} (M : GradedModule A) (N : LGrMod(A)) : GrdO :=
  (tensorFunctor M).obj N

/-- A graded right `A`-module is flat when relative tensoring with it is exact. -/
@[stacks 0FSA "relative graded flatness"]
abbrev IsFlat {A : DGA(𝒪)} (M : GradedModule A) : Prop :=
  CategoryTheory.Bimod.IsFlat (toBimod M)

/-- Relatively flat graded right `A`-modules as an object property. -/
abbrev flatObjects (A : DGA(𝒪)) : ObjectProperty (GradedModule A) :=
  fun M ↦ IsFlat M

/-- Relative graded flatness is exactness of the balanced tensor functor. -/
theorem isFlat_iff {A : DGA(𝒪)} (M : GradedModule A) :
    IsFlat M ↔ exactFunctor LGrMod(A) GrdO (tensorFunctor M) := Iff.rfl

/-- Relative graded tensor is the underlying coequalizer-based balanced tensor product. -/
@[simp]
theorem tensor_eq {A : DGA(𝒪)} (M : GradedModule A) (N : LGrMod(A)) :
    tensor M N = ((toBimod M).tensorBimod N).X := rfl

end DifferentialGradedAlgebra.GradedModule

end

end SheafOfModules.RingedSite

end
