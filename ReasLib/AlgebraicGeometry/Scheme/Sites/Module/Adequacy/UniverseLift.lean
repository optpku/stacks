/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Underlying
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineEvaluation

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u v

namespace ModuleValuedFunctor

/-- Tensor extension with its module carriers lifted by one universe. -/
noncomputable def tensorExtensionLifted (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ ModuleValuedFunctor.bundled.{u, u + 1} A where
  obj M :=
    { obj := fun B ↦
        (ModuleCat.uliftFunctor.{u + 1, u} B.right).obj
          (((tensorExtensionFunctor A).obj M).obj B)
      map := fun {B B'} f ↦
        (ModuleCat.uliftFunctor.{u + 1, u} B.right).map
          (((tensorExtensionFunctor A).obj M).map f)
      map_id := sorry
      map_comp := sorry }
  map f :=
    { app := fun B ↦
        (ModuleCat.uliftFunctor.{u + 1, u} B.right).map
          (((tensorExtensionFunctor A).map f).app B)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Objectwise, `tensorExtensionLifted` is the canonical universe lift of tensor extension. -/
theorem tensorExtensionLifted_obj_obj (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
    (B : Under A) :
    ((tensorExtensionLifted A).obj M).obj B =
      (ModuleCat.uliftFunctor.{u + 1, u} B.right).obj
        (((tensorExtensionFunctor A).obj M).obj B) := sorry

/-- The additive-group-valued view of lifted tensor extension. -/
noncomputable def tensorExtensionUnderlyingLifted (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u + 1}) :=
  tensorExtensionLifted A ⋙ forget A

/-- The underlying view of lifted tensor extension evaluates through
`ModuleValuedFunctor.toFunctor`. -/
theorem tensorExtensionUnderlyingLifted_obj (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (tensorExtensionUnderlyingLifted A).obj M =
      ((tensorExtensionLifted A).obj M).toFunctor := sorry

end ModuleValuedFunctor

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- Affine evaluation of a module sheaf whose module carriers live in universe `v`. -/
noncomputable def affineEvaluationLifted
    (ℱ : RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S))
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) :
    ModuleValuedFunctor.{u, v} A where
  obj B :=
    (ModuleCat.restrictScalars (affineObjectRingHom f B).hom).obj
      (ℱ.val.obj (op (affineObject f B)))
  map := fun {B B'} g ↦
    ModuleCat.semilinearMapAddEquiv g.right.hom _ _
      { toFun := fun x ↦ ℱ.val.map (affineObjectMap f g).op x
        map_add' := sorry
        map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The object assigned by lifted affine evaluation is the restriction of scalars of
the value of the sheaf on the corresponding affine object. -/
theorem affineEvaluationLifted_obj
    (ℱ : RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S))
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) (B : Under A) :
    (affineEvaluationLifted ℱ A f).obj B =
      (ModuleCat.restrictScalars (affineObjectRingHom f B).hom).obj
        (ℱ.val.obj (op (affineObject f B))) := sorry

/-- The additive-group-valued view of affine evaluation in coefficient universe `v`. -/
noncomputable def affineEvaluationUnderlyingLifted
    (ℱ : RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S))
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) :
    Under A ⥤ AddCommGrpCat.{v} :=
  (ModuleValuedFunctor.forget A).obj (affineEvaluationLifted ℱ A f)

/-- The underlying lifted affine evaluation is the ordinary functor of the bundled
module-valued affine evaluation. -/
theorem affineEvaluationUnderlyingLifted_eq
    (ℱ : RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S))
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) :
    affineEvaluationUnderlyingLifted ℱ A f = (affineEvaluationLifted ℱ A f).toFunctor :=
  sorry

/-- Adequacy of a big-site module sheaf with coefficient universe independent of the
universe of the base scheme. -/
abbrev IsAdequateWith
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{v}))
    (affineEvaluation :
      RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{v})
    (ℱ : RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S)) : Prop :=
  IsAdequate underline affineEvaluation ℱ

/-- `IsAdequateWith` is characterized by adequacy on the members of one affine cover. -/
theorem isAdequateWith_iff
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{v}))
    (affineEvaluation :
      RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{v})
    (ℱ : RingedSite.ModuleCat.{v} (StandardTopology.Big.ringedSite τ S)) :
    IsAdequateWith underline affineEvaluation ℱ ↔
      ∃ (ι : Type u) (A : ι → CommRingCat.{u})
          (f : (i : ι) → Scheme.Spec.obj (op (A i)) ⟶ S),
        SemiRepresentableFamily.Over.IsCovering τ.precoverage
            (SemiRepresentableFamily.Over.ofArrows
              (fun i ↦ Scheme.Spec.obj (op (A i))) f) ∧
          ∀ i, Adequate (A i) (underline (A i)) (affineEvaluation ℱ (A i) (f i)) :=
  sorry

/-- In the scheme universe, `IsAdequateWith` agrees with the original adequacy predicate. -/
theorem isAdequateWith_iff_isAdequate
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (affineEvaluation :
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u})
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)) :
    IsAdequateWith underline affineEvaluation ℱ ↔
      IsAdequate underline affineEvaluation ℱ := sorry

end SheafOfModules
