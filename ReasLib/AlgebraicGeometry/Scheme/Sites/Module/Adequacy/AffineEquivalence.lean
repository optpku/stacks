/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Coreflection
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.AdequateCategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequateCategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEvaluation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineEvaluation.Underlying

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- The full category of module sheaves on the big `τ`-site of `Spec A` whose
affine evaluation at the identity is tensor-adequate. -/
abbrev AffineAdeq (τ : StandardTopology) (A : CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory
    (fun ℱ : RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) ↦
      ModuleValuedFunctor.TensorAdequate
        (affineEvaluation ℱ.val A (𝟙 (Scheme.Spec.obj (op A)))))

/-- On an affine base, a module sheaf is adequate precisely when its affine
evaluation at the identity is tensor-adequate. -/
theorem isAdequate_iff_affineEvaluationIdentity (τ : StandardTopology)
    (A : CommRingCat.{u})
    (ℱ : RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))) :
    @SheafOfModules.IsAdequate (Scheme.Spec.obj (op A)) τ
        ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying (Scheme.Spec.obj (op A)) τ) ℱ ↔
      ModuleValuedFunctor.TensorAdequate
        (affineEvaluation ℱ.val A (𝟙 (Scheme.Spec.obj (op A)))) := sorry

/-- Affine evaluation sends a morphism of module presheaves to the componentwise
linear morphism of module-valued functors. -/
noncomputable def affineEvaluationHom {A : CommRingCat.{u}}
    (f : Scheme.Spec.obj (op A) ⟶ S)
    {ℱ 𝒢 : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj}
    (φ : ℱ ⟶ 𝒢) :
      ModuleValuedFunctor.Hom (affineEvaluation ℱ A f) (affineEvaluation 𝒢 A f) where
  app B := (ModuleCat.restrictScalars (affineObjectRingHom f B).hom).map
    (φ.app (op (affineObject f B)))
  naturality := sorry

/-- The component of `affineEvaluationHom f φ` at an `A`-algebra is restriction
of scalars applied to the corresponding component of `φ`. -/
theorem affineEvaluationHom_app {A : CommRingCat.{u}}
    (f : Scheme.Spec.obj (op A) ⟶ S)
    {ℱ 𝒢 : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj}
    (φ : ℱ ⟶ 𝒢) (B : Under A) :
    (affineEvaluationHom f φ).app B =
      (ModuleCat.restrictScalars (affineObjectRingHom f B).hom).map
        (φ.app (op (affineObject f B))) := sorry

/-- Affine evaluation as a functor from module presheaves on the big site of `S`
to module-valued functors on `A`-algebras. -/
noncomputable def affineEvaluationFunctor (A : CommRingCat.{u})
    (f : Scheme.Spec.obj (op A) ⟶ S) :
    PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj ⥤
      ModuleValuedFunctor.bundled A where
  obj ℱ := affineEvaluation ℱ A f
  map φ := affineEvaluationHom f φ
  map_id := sorry
  map_comp := sorry

/-- The object map of `affineEvaluationFunctor A f` is affine evaluation. -/
theorem affineEvaluationFunctor_obj (A : CommRingCat.{u})
    (f : Scheme.Spec.obj (op A) ⟶ S)
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj) :
    (affineEvaluationFunctor A f).obj ℱ = affineEvaluation ℱ A f := sorry

/-- The morphism map in `affineEvaluationFunctor A f` is computed componentwise
by restriction of scalars. -/
theorem affineEvaluationFunctor_map_app (A : CommRingCat.{u})
    (f : Scheme.Spec.obj (op A) ⟶ S)
    {ℱ 𝒢 : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj}
    (φ : ℱ ⟶ 𝒢) (B : Under A) :
    ((affineEvaluationFunctor A f).map φ).app B =
      (ModuleCat.restrictScalars (affineObjectRingHom f B).hom).map
        (φ.app (op (affineObject f B))) := sorry

/-- Affine evaluation as a functor from module sheaves on the big site of `S`. -/
noncomputable def affineEvaluationSheafFunctor (A : CommRingCat.{u})
    (f : Scheme.Spec.obj (op A) ⟶ S) :
    RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) ⥤
      ModuleValuedFunctor.bundled A :=
  SheafOfModules.forget (StandardTopology.Big.structureSheaf τ S) ⋙
    affineEvaluationFunctor A f

/-- The object map of `affineEvaluationSheafFunctor A f` evaluates the underlying
module presheaf. -/
theorem affineEvaluationSheafFunctor_obj (A : CommRingCat.{u})
    (f : Scheme.Spec.obj (op A) ⟶ S)
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)) :
    (affineEvaluationSheafFunctor A f).obj ℱ = affineEvaluation ℱ.val A f := sorry

/-- The canonical affine-evaluation functor from adequate module sheaves on
`Spec A` to adequate module-valued functors on `A`-algebras. -/
noncomputable def affineEvaluationAdequate (τ : StandardTopology) (A : CommRingCat.{u}) :
    AffineAdeq τ A ⥤ ModuleValuedFunctor.TensorAdeq A :=
  ObjectProperty.lift
    (ModuleValuedFunctor.TensorAdequate (A := A))
    (ObjectProperty.ι
      (fun ℱ : RingedSite.ModuleCat.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) ↦
        ModuleValuedFunctor.TensorAdequate
          (affineEvaluation ℱ.val A (𝟙 (Scheme.Spec.obj (op A))))) ⋙
      affineEvaluationSheafFunctor A (𝟙 (Scheme.Spec.obj (op A))))
    (fun ℱ ↦ ℱ.property)

/-- On objects, `affineEvaluationAdequate τ A` is affine evaluation at the
identity of `Spec A`. -/
theorem affineEvaluationAdequate_obj (τ : StandardTopology) (A : CommRingCat.{u})
    (ℱ : AffineAdeq τ A) :
    ((affineEvaluationAdequate τ A).obj ℱ).obj =
      affineEvaluation ℱ.obj.val A (𝟙 (Scheme.Spec.obj (op A))) := sorry

/-- Affine evaluation induces an equivalence between affine-adequate module
sheaves and adequate module-valued functors. -/
noncomputable instance affineEvaluationAdequateIsEquivalence
    (τ : StandardTopology) (A : CommRingCat.{u}) :
    (affineEvaluationAdequate τ A).IsEquivalence := sorry

end SheafOfModules

namespace SheafOfModules.AffineAdeq

variable {τ : StandardTopology}

/-- The inclusion of affine-adequate module sheaves into all module sheaves on
the big `τ`-site of `Spec A`. -/
noncomputable abbrev inclusion (τ : StandardTopology) (A : CommRingCat.{u}) :
    AffineAdeq τ A ⥤ RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) :=
  ObjectProperty.ι
    (fun ℱ : RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) ↦
      ModuleValuedFunctor.TensorAdequate
        (affineEvaluation ℱ.val A (𝟙 (Scheme.Spec.obj (op A)))))

/-- The object map of the affine-adequate inclusion is the underlying module
sheaf. -/
@[simp] theorem inclusion_obj (τ : StandardTopology) (A : CommRingCat.{u})
    (ℱ : AffineAdeq τ A) : (inclusion τ A).obj ℱ = ℱ.obj := rfl

/-- The affine-adequate inclusion has a right adjoint. -/
noncomputable instance inclusionIsLeftAdjoint (τ : StandardTopology)
    (A : CommRingCat.{u}) :
    (inclusion τ A).IsLeftAdjoint := sorry

/-- The counit of the affine-adequate inclusion's canonical adjunction is an
isomorphism on every included affine-adequate module sheaf. -/
noncomputable instance inclusionCounitAppIsIso (τ : StandardTopology)
    (A : CommRingCat.{u}) (ℱ : AffineAdeq τ A) :
    IsIso ((Adjunction.ofIsLeftAdjoint (inclusion τ A)).counit.app
      ((inclusion τ A).obj ℱ)) := by
  apply Adjunction.isIso_counit_app_of_iso
  exact Iso.refl _

end SheafOfModules.AffineAdeq
