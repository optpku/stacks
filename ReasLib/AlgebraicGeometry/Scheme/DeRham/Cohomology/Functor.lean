module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.CategoryTheory.GradedObject

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Cohomology

variable {k : Type u} [Field k]

/-- Canonical restricted de Rham pullback over a field commutes with base scalars. -/
theorem restrictedPullback_smul_overField {X Y : SchemeOverField k} (f : X ⟶ Y)
    (i : ℤ) (a : k) (x : cohomologyOverAffineBase Y.hom i) :
    (restrictedPullback (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩) i
      (hPull := RingedSite.Hom.modulePushforwardToDerived.hasRightDerived
        (coefficientHom (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩)))).hom
        (a • x : cohomologyOverAffineBase Y.hom i) =
      @SMul.smul k (cohomologyOverAffineBase X.hom i) inferInstance a
        ((restrictedPullback (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩) i
        (hPull := RingedSite.Hom.modulePushforwardToDerived.hasRightDerived
          (coefficientHom (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩)))).hom x :
            cohomologyOverAffineBase X.hom i) := by
  sorry

/-- The base-field-linear canonical pullback on relative de Rham cohomology. -/
def pullbackOverField {X Y : SchemeOverField k} (f : X ⟶ Y) (i : ℤ) :
    cohomologyOverAffineBase Y.hom i ⟶ cohomologyOverAffineBase X.hom i :=
  ModuleCat.ofHom (R := k)
    (X := cohomologyOverAffineBase Y.hom i) (Y := cohomologyOverAffineBase X.hom i)
    { toFun := fun x ↦ (restrictedPullback (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩) i
        (hPull := RingedSite.Hom.modulePushforwardToDerived.hasRightDerived
          (coefficientHom (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩)))).hom x
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := restrictedPullback_smul_overField f i }

/-- Base-field-linear pullback has the underlying function of canonical restricted pullback. -/
theorem pullbackOverField_apply {X Y : SchemeOverField k} (f : X ⟶ Y) (i : ℤ)
    (x : cohomologyOverAffineBase Y.hom i) :
    (pullbackOverField f i).hom x =
      (restrictedPullback (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩) i
        (hPull := RingedSite.Hom.modulePushforwardToDerived.hasRightDerived
          (coefficientHom (show CommSq f.left X.hom Y.hom (𝟙 _) from
        ⟨f.w.trans (Category.comp_id X.hom).symm⟩)))).hom x := rfl

/-- Pullback by the identity scheme morphism is the identity on de Rham cohomology. -/
theorem pullbackOverField_id (X : SchemeOverField k) (i : ℤ) :
    pullbackOverField (𝟙 X) i = 𝟙 (cohomologyOverAffineBase X.hom i) := by
  sorry

/-- Canonical de Rham pullback reverses composition of morphisms over a field. -/
theorem pullbackOverField_comp {X Y Z : SchemeOverField k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℤ) :
    pullbackOverField (f ≫ g) i = pullbackOverField g i ≫ pullbackOverField f i := by
  sorry

/-- Relative de Rham cohomology as a contravariant graded module-valued functor. -/
def gradedFunctor (k : Type u) [Field k] :
    (SchemeOverField k)ᵒᵖ ⥤ GradedObject ℤ (ModuleCat.{u} k) where
  obj X i := cohomologyOverAffineBase X.unop.hom i
  map f i := pullbackOverField f.unop i
  map_id X := funext fun i ↦ pullbackOverField_id X.unop i
  map_comp f g := funext fun i ↦ pullbackOverField_comp g.unop f.unop i

/-- The degree components of the graded de Rham functor are affine-base cohomology. -/
theorem gradedFunctor_obj (X : SchemeOverField k) (i : ℤ) :
    (gradedFunctor k).obj (Opposite.op X) i = cohomologyOverAffineBase X.hom i := rfl

/-- The graded de Rham functor acts by canonical base-field-linear pullback. -/
theorem gradedFunctor_map {X Y : SchemeOverField k} (f : X ⟶ Y) (i : ℤ) :
    (gradedFunctor k).map f.op i = pullbackOverField f i := rfl

end AlgebraicGeometry.Scheme.DeRham.Cohomology
