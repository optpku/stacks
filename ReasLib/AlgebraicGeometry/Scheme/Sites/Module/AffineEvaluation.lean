/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- The affine object over a scheme obtained from an algebra and a map from its spectrum. -/
noncomputable def affineObject {A : CommRingCat.{u}}
    (f : Scheme.Spec.obj (op A) ⟶ S) (B : Under A) : Over S :=
  Over.mk (Spec.map B.hom ≫ f)

/-- Compatibility of the affine-object structure map with algebra morphisms. -/
theorem affineObjectMap_fac {A : CommRingCat.{u}}
    (f : Scheme.Spec.obj (op A) ⟶ S) {B B' : Under A} (g : B ⟶ B') :
    Spec.map g.right ≫ (affineObject f B).hom = (affineObject f B').hom := sorry

/-- The morphism of affine objects induced by a morphism of algebras. -/
noncomputable def affineObjectMap {A : CommRingCat.{u}}
    (f : Scheme.Spec.obj (op A) ⟶ S) {B B' : Under A} (g : B ⟶ B') :
    affineObject f B' ⟶ affineObject f B :=
  Over.homMk (Spec.map g.right) (affineObjectMap_fac f g)

/-- The canonical map from an algebra to sections on its associated affine object. -/
noncomputable def affineObjectRingHom {A : CommRingCat.{u}}
    (f : Scheme.Spec.obj (op A) ⟶ S) (B : Under A) :
    (forget₂ CommRingCat RingCat).obj B.right ⟶
      (StandardTopology.Big.structureSheaf τ S).obj.obj (op (affineObject f B)) :=
  (forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso B.right).inv

/-- The module obtained by evaluating a module presheaf on an affine object. -/
noncomputable abbrev affineEvaluationObj {A : CommRingCat.{u}}
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (f : Scheme.Spec.obj (op A) ⟶ S) (B : Under A) : ModuleCat.{u} B.right :=
  (ModuleCat.restrictScalars (affineObjectRingHom f B).hom).obj
    (ℱ.obj (op (affineObject f B)))

/-- Additivity of restriction between affine evaluations. -/
theorem affineEvaluationMap_add {A : CommRingCat.{u}}
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (f : Scheme.Spec.obj (op A) ⟶ S) {B B' : Under A} (g : B ⟶ B')
    (x y : affineEvaluationObj ℱ f B) :
    ℱ.map (affineObjectMap f g).op (x + y) =
      ℱ.map (affineObjectMap f g).op x + ℱ.map (affineObjectMap f g).op y := sorry

/-- The underlying function of an affine-evaluation restriction map. -/
noncomputable def affineEvaluationMapFun {A : CommRingCat.{u}}
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (f : Scheme.Spec.obj (op A) ⟶ S) {B B' : Under A} (g : B ⟶ B') :
    affineEvaluationObj ℱ f B → affineEvaluationObj ℱ f B' :=
  fun x ↦ ℱ.map (affineObjectMap f g).op x

/-- Semilinearity of restriction between affine evaluations. -/
theorem affineEvaluationMap_smul {A : CommRingCat.{u}}
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (f : Scheme.Spec.obj (op A) ⟶ S) {B B' : Under A} (g : B ⟶ B')
    (r : B.right) (x : affineEvaluationObj ℱ f B) :
    affineEvaluationMapFun ℱ f g (r • x) =
      g.right r • affineEvaluationMapFun ℱ f g x := sorry

/-- The linear restriction map between affine evaluations. -/
noncomputable def affineEvaluationMap {A : CommRingCat.{u}}
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (f : Scheme.Spec.obj (op A) ⟶ S) {B B' : Under A} (g : B ⟶ B') :
    affineEvaluationObj ℱ f B ⟶
      (ModuleCat.restrictScalars g.right.hom).obj (affineEvaluationObj ℱ f B') :=
  ModuleCat.semilinearMapAddEquiv g.right.hom _ _
    { toFun := affineEvaluationMapFun ℱ f g
      map_add' := affineEvaluationMap_add ℱ f g
      map_smul' := affineEvaluationMap_smul ℱ f g }

/-- Restriction along an identity is the identity. -/
theorem affineEvaluationMap_id {A : CommRingCat.{u}}
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (f : Scheme.Spec.obj (op A) ⟶ S) (B : Under A) (x : affineEvaluationObj ℱ f B) :
    affineEvaluationMap ℱ f (𝟙 B) x = x := sorry

/-- Restriction respects composition. -/
theorem affineEvaluationMap_comp {A : CommRingCat.{u}}
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (f : Scheme.Spec.obj (op A) ⟶ S) {B B' B'' : Under A}
    (g : B ⟶ B') (h : B' ⟶ B'') (x : affineEvaluationObj ℱ f B) :
    affineEvaluationMap ℱ f (g ≫ h) x =
      affineEvaluationMap ℱ f h (affineEvaluationMap ℱ f g x) := sorry

/-- The module-valued functor obtained by affine evaluation. -/
noncomputable def affineEvaluation
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) :
    ModuleValuedFunctor.{u, u} A where
  obj := affineEvaluationObj ℱ f
  map := affineEvaluationMap ℱ f
  map_id := affineEvaluationMap_id ℱ f
  map_comp := affineEvaluationMap_comp ℱ f

end SheafOfModules
