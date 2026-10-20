/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Underlying
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineEvaluation.Underlying
public import stacks_project.Chap46.Definition_46_3_2_Instances

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u v

namespace ModuleValuedFunctor

#check (ModuleValuedFunctor.forget :
    (A : CommRingCat.{u}) → ModuleValuedFunctor.{u, v} A ⥤
      (Under A ⥤ AddCommGrpCat.{v}))
#check (ModuleValuedFunctor.forget_obj :
    ∀ (A : CommRingCat.{u}) (F : ModuleValuedFunctor.{u, v} A),
      (ModuleValuedFunctor.forget A).obj F = F.toFunctor)
#check (ModuleValuedFunctor.forget_map_app :
    ∀ (A : CommRingCat.{u}) {F G : ModuleValuedFunctor.{u, v} A}
      (φ : F ⟶ G) (B : Under A),
      ((ModuleValuedFunctor.forget A).map φ).app B =
        (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (φ.app B))
#check (ModuleValuedFunctor.tensorExtensionUnderlying :
    (A : CommRingCat.{u}) → ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
#check (ModuleValuedFunctor.tensorExtensionUnderlying_obj :
    ∀ (A : CommRingCat.{u}) (M : ModuleCat.{u} A),
      (ModuleValuedFunctor.tensorExtensionUnderlying A).obj M =
        ((ModuleValuedFunctor.tensorExtensionFunctor A).obj M).toFunctor)

end ModuleValuedFunctor

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

#check (SheafOfModules.affineEvaluationUnderlying :
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)) →
      (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
        Under A ⥤ AddCommGrpCat.{u})
#check (SheafOfModules.affineEvaluationUnderlying_eq :
    ∀ (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S))
      (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S),
      SheafOfModules.affineEvaluationUnderlying ℱ A f =
        (SheafOfModules.affineEvaluation ℱ.val A f).toFunctor)

end SheafOfModules
