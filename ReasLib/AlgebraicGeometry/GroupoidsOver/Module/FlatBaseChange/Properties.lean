/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent.Properties
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange.Properties

/-! # Closure operations on locally quasi-coherent modules with flat base change -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver.LQCohFbc

variable {S : Scheme.{u}}

/-- Locally quasi-coherent étale modules with flat base change are closed under colimits. -/
instance closedUnderColimitsOfShape (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J] :
    (lqcohFbc X).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := sorry

/-- Fppf realization preserves all universe-compatible colimits. -/
instance toFppf_preservesColimitsOfShape (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J] [HasColimitsOfShape J AddCommGrpCat.{u}] :
    PreservesColimitsOfShape J (toFppf X) := sorry

/-- The underlying étale module of a colimit of locally quasi-coherent modules
with flat base change is already an fppf sheaf. -/
theorem colimit_isSheaf_fppf {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} [Category.{w} J] (F : J ⥤ LQCohFbc X) [HasColimit F] :
    Presheaf.IsSheaf (ringedSite X).siteTopology
      (etaleModulePresheaf ((inclusion X).obj (colimit F))).presheaf :=
  ((toFppf X).obj (colimit F)).isSheaf

/-- The ambient tensor product of locally quasi-coherent modules with flat
base change, equipped with the same two properties. -/
def tensor {X : GroupoidsOver S} [AlgebraicStack X] (F G : LQCohFbc X) :
    LQCohFbc X :=
  ⟨moduleTensorEtale F.obj G.obj,
    (lqcohFbc_iff _).mpr
      ⟨@isLocallyQuasiCoherent_tensor S X F.obj G.obj
        ((lqcohFbc_iff _).mp F.property).1 ((lqcohFbc_iff _).mp G.property).1,
       @HasFlatBaseChange.tensor S X _ F.obj G.obj
        ((lqcohFbc_iff _).mp F.property).2 ((lqcohFbc_iff _).mp G.property).2⟩⟩

/-- The underlying module of the tensor is the ambient étale tensor product. -/
theorem tensor_obj {X : GroupoidsOver S} [AlgebraicStack X] (F G : LQCohFbc X) :
    (tensor F G).obj = moduleTensorEtale F.obj G.obj := rfl

/-- Internal Hom from a finitely presented étale module into a locally
quasi-coherent module with flat base change is locally quasi-coherent with flat base change. -/
theorem mem_sheafHom {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [F.IsFinitePresentation] (G : LQCohFbc X) :
    lqcohFbc X (moduleSheafHomEtale F G.obj) := sorry

/-- The ambient internal Hom from a finitely presented module into a locally
quasi-coherent module with flat base change, equipped with those properties. -/
def sheafHom {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [F.IsFinitePresentation] (G : LQCohFbc X) : LQCohFbc X :=
  ⟨moduleSheafHomEtale F G.obj, mem_sheafHom F G⟩

/-- The underlying module of internal Hom is the ambient étale internal Hom. -/
theorem sheafHom_obj {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [F.IsFinitePresentation] (G : LQCohFbc X) :
    (sheafHom F G).obj = moduleSheafHomEtale F G.obj := rfl

end AlgebraicGeometry.GroupoidsOver.LQCohFbc
