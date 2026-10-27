/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Monoidal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction

/-! # Symmetric monoidal modules with flat base change -/

@[expose] public section

-- Private comparison maps occur only in bodies of the public canonical constructions.
set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite PresheafOfModules CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace LQCohFbc

/-- The étale tensor unit is locally quasi-coherent with flat base change. -/
theorem unit_mem (X : GroupoidsOver S) [AlgebraicStack X] :
    lqcohFbc X (𝟙_ (etaleModules X)) := sorry

/-- Local quasi-coherence and flat base change are stable under tensor and unit. -/
instance isMonoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (lqcohFbc X).IsMonoidal where
  prop_unit := unit_mem X
  prop_tensor F G hF hG := (tensor ⟨F, hF⟩ ⟨G, hG⟩).property

/-- The inherited tensor is the canonical étale tensor with closure certificates. -/
theorem tensorObj_eq (X : GroupoidsOver S) [AlgebraicStack X] (F G : LQCohFbc X) :
    (F ⊗ G : LQCohFbc X) = tensor F G := rfl

/-- The full-subcategory inclusion preserves the unit and tensor strongly. -/
instance inclusion_monoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (inclusion X).Monoidal := inferInstance

/-- The full-subcategory inclusion preserves tensor symmetry. -/
instance inclusion_braided (X : GroupoidsOver S) [AlgebraicStack X] :
    (inclusion X).Braided := inferInstance

end LQCohFbc

/-- The tensor product of two morphisms of `LQCoh^{fbc}` modules, computed as
the étale module tensor map of the underlying morphisms. -/
def LQCohFbc.tensorHom {X : GroupoidsOver S} [AlgebraicStack X]
    {F₁ F₂ G₁ G₂ : LQCohFbc X} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    LQCohFbc.tensor F₁ G₁ ⟶ LQCohFbc.tensor F₂ G₂ :=
  ObjectProperty.homMk (moduleTensorMap.{u + 1, u, u} f.hom g.hom)

/-- The underlying étale morphism of `LQCohFbc.tensorHom f g` is the module
tensor map. -/
theorem LQCohFbc.tensorHom_hom {X : GroupoidsOver S} [AlgebraicStack X]
    {F₁ F₂ G₁ G₂ : LQCohFbc X} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    (LQCohFbc.tensorHom f g).hom =
      moduleTensorMap.{u + 1, u, u} f.hom g.hom :=
  rfl


namespace LQCohFbc

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- The pure-tensor section map into the étale sheaf tensor. -/
private def tensorSections (F G : LQCohFbc X) :
    restrictPresheafToCommEtale X
      (Monoidal.tensorObj ((toCommFppfModules X).obj ((toFppf X).obj F)).val
        ((toCommFppfModules X).obj ((toFppf X).obj G)).val) ⟶
      (tensor F G).obj.val := by
  let e : (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance X.etaleTopology
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).obj
        (Monoidal.tensorObj F.obj.val G.obj.val) ≅ (tensor F G).obj :=
    (Functor.Monoidal.μIso
      (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance X.etaleTopology
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X))
      F.obj.val G.obj.val).symm ≪≫
    tensorIso
      (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance X.etaleTopology
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X) F.obj)
      (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance X.etaleTopology
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X) G.obj)
  let g : Monoidal.tensorObj F.obj.val G.obj.val ⟶ (tensor F G).obj.val := (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance X.etaleTopology
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X) (Monoidal.tensorObj F.obj.val G.obj.val)
      (tensor F G).obj) e.hom
  let aF : ((toCommFppfModules X).obj ((toFppf X).obj F)).val ⟶ fppfViewPresheaf F.obj :=
    { app := fun _ => 𝟙 _, naturality := by intros; rfl }
  let aG : ((toCommFppfModules X).obj ((toFppf X).obj G)).val ⟶ fppfViewPresheaf G.obj :=
    { app := fun _ => 𝟙 _, naturality := by intros; rfl }
  let h := Monoidal.tensorHom aF aG ≫
    PresheafOfModules.Restriction.tensorComparison (fppfCoefficientToEtale X)
      F.obj.val G.obj.val ≫
    (restrictScalars.{u} (presheafStructureMap (fppfCoefficientToEtale X))).map g
  exact (restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).map h ≫
    (etaleOfFppfViewToOriginal (tensor F G).obj
      (@isSheaf_fppf_of_lqcohFbc S X _ (tensor F G).obj
        ((lqcohFbc_iff _).mp (tensor F G).property).1
        ((lqcohFbc_iff _).mp (tensor F G).property).2)).val

/-- The fppf tensor comparison extends the pure-tensor map by sheafification. -/
def toFppf_tensorator (F G : LQCohFbc X) :
    (toFppf X).obj F ⊗ (toFppf X).obj G ⟶ (toFppf X).obj (tensor F G) :=
  (fromCommFppfModules X).map
    ((associatedModuleTensorIso
        ((toCommFppfModules X).obj ((toFppf X).obj F))
        ((toCommFppfModules X).obj ((toFppf X).obj G))).inv ≫
      fromFppfSheafification (tensor F G).obj
        (@isSheaf_fppf_of_lqcohFbc S X _ (tensor F G).obj
          ((lqcohFbc_iff _).mp (tensor F G).property).1
          ((lqcohFbc_iff _).mp (tensor F G).property).2)
        _ (tensorSections F G) ≫
      { val := { app := fun _ => 𝟙 _, naturality := by intros; rfl } }) ≫
    ((commFppfModulesEquivalence X).unitIso.app ((toFppf X).obj (tensor F G))).inv

/-- The fppf unit comparison is induced by the structure-module unit maps. -/
def toFppf_unit (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟙_ (RingedSite.ModuleCat.{u} (ringedSite X)) ⟶ (toFppf X).obj (𝟙_ (LQCohFbc X)) := by
  let h : (@unitModule.{u + 1, u, u} X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf) (commAssociatedStructureSheaf X .fppf) :
      commAssociatedModules X .fppf) ⟶
      (toCommFppfModules X).obj ((toFppf X).obj (𝟙_ (LQCohFbc X))) :=
    { val := {
        app := fun U => (@unitIsoTensorUnit.{u + 1, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X) (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).hom.val.app U
        naturality := fun f =>
          (@unitIsoTensorUnit.{u + 1, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X) (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).hom.val.naturality f } }
  exact (fromCommFppfModules X).map
    ((@unitIsoTensorUnit.{u + 1, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf) (associatedTopology_hasWeakSheafify X .fppf) (associatedTopology_wEqualsLocallyBijective X .fppf) (commAssociatedStructureSheaf X .fppf)).inv ≫ h) ≫
    ((commFppfModulesEquivalence X).unitIso.app
      ((toFppf X).obj (𝟙_ (LQCohFbc X)))).inv

/-- Fppf realization preserves the canonical unit and tensor maps coherently. -/
instance toFppf_laxMonoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (toFppf X).LaxMonoidal := by
  refine {
    ε := toFppf_unit X
    μ := toFppf_tensorator
    μ_natural_left := ?_
    μ_natural_right := ?_
    associativity := ?_
    left_unitality := ?_
    right_unitality := ?_ }
  all_goals sorry

/-- The structure-module comparison for fppf realization is invertible. -/
instance toFppf_unit_isIso (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (Functor.LaxMonoidal.ε (toFppf X)) := sorry

/-- The fppf tensor comparison is invertible. -/
instance toFppf_tensorator_isIso (F G : LQCohFbc X) :
    IsIso (Functor.LaxMonoidal.μ (toFppf X) F G) := sorry

/-- Fppf realization is strong monoidal for the canonical comparisons. -/
instance toFppf_monoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (toFppf X).Monoidal := Functor.Monoidal.ofLaxMonoidal (toFppf X)

/-- Fppf realization preserves the symmetry of module tensors. -/
instance toFppf_braided (X : GroupoidsOver S) [AlgebraicStack X] :
    (toFppf X).Braided where
  braided := sorry

end LQCohFbc

end AlgebraicGeometry.GroupoidsOver
