module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_33_2_Equivalence
public import stacks_project.Chap85.Lemma_85_36_2_Hypercovering

/-!
# Descent equivalence for proper hypercoverings

If `a : U ⟶ X` is a proper hypercovering, then `a⁻¹` identifies sheaves on
`X_spaces,étale` with cartesian sheaves on `U_spaces,étale`, with quasi-inverse
`a_*`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Functor
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
variable (A : Type (u + 2)) [Category.{u + 1} A]
variable [∀ n : SimplexCategoryᵒᵖ, HasWeakSheafify (spacesEtaleTopology (U.obj n)) A]
variable [HasWeakSheafify (spacesEtaleTopology X) A]
variable [HasWeakSheafify (spacesEtaleTotalTopology U) A]
variable [∀ P : (spacesEtaleSite X)ᵒᵖ ⥤ A, (augmentationFunctor U a).op.HasLeftKanExtension P]

/-- Inverse image `a⁻¹` along a proper hypercovering is full. -/
theorem properInverseImage_full (ha : IsProperHypercovering a) :
    (inverseImage U A a).Full :=
  sorry

/-- Inverse image `a⁻¹` along a proper hypercovering is faithful. -/
theorem properInverseImage_faithful (ha : IsProperHypercovering a) :
    (inverseImage U A a).Faithful :=
  sorry

/-- Inverse image `a⁻¹` along a proper hypercovering is fully faithful. -/
def properInverseImage_fullyFaithful (ha : IsProperHypercovering a) :
    (inverseImage U A a).FullyFaithful :=
  @FullyFaithful.ofFullyFaithful _ _ _ _ (inverseImage U A a)
    (properInverseImage_full a A ha) (properInverseImage_faithful a A ha)

/-- The unit of `a⁻¹ ⊣ a_*` is an isomorphism along a proper hypercovering. -/
theorem proper_unit_app_isIso (ha : IsProperHypercovering a)
    (F : Sheaf (spacesEtaleTopology X) A) :
    IsIso (((augmentationFunctor U a).sheafAdjunctionContinuous A
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).unit.app F) :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism precisely on cartesian sheaves. -/
theorem proper_counit_app_isIso_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) A) :
    IsIso (((augmentationFunctor U a).sheafAdjunctionContinuous A
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).counit.app G) ↔
      IsCartesian U A G :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism on a cartesian sheaf. -/
theorem proper_counit_app_isIso_of_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) A) (h : IsCartesian U A G) :
    IsIso (((augmentationFunctor U a).sheafAdjunctionContinuous A
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).counit.app G) :=
  sorry

/-- A sheaf on `U_étale` lies in the essential image of `a⁻¹` if and only if it is
cartesian. -/
theorem proper_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) A) :
    (inverseImage U A a).essImage G ↔ IsCartesian U A G :=
  sorry

/-- The functor `a⁻¹` corestricted to cartesian sheaves on `U_étale`. -/
def properCartesianFunctor : Sheaf (spacesEtaleTopology X) A ⥤ Cartesian U A :=
  (cartesianProperty U A).lift (inverseImage U A a) fun F ↦
    inverseImage_isCartesian U A a F

/-- On objects, `properCartesianFunctor` is inverse image along the spaces-étale
augmentation. -/
theorem properCartesianFunctor_obj (F : Sheaf (spacesEtaleTopology X) A) :
    ((properCartesianFunctor a A).obj F).obj = (inverseImage U A a).obj F :=
  sorry

/-- The functor sending a cartesian sheaf on `U_étale` to `a_*` of its underlying
sheaf. -/
def properCartesianInverse : Cartesian U A ⥤ Sheaf (spacesEtaleTopology X) A :=
  (cartesianProperty U A).ι ⋙ directImage U A a

/-- On objects, `properCartesianInverse` is direct image along the spaces-étale
augmentation. -/
theorem properCartesianInverse_obj (G : Cartesian U A) :
    (properCartesianInverse a A).obj G = (directImage U A a).obj G.obj :=
  sorry

/-- Naturality of the unit components of proper-hypercovering descent. -/
theorem properCartesianUnitIso_naturality (ha : IsProperHypercovering a)
    {F G : Sheaf (spacesEtaleTopology X) A} (f : F ⟶ G) :
    (𝟭 (Sheaf (spacesEtaleTopology X) A)).map f ≫
        (@asIso _ _ _ _
          (((augmentationFunctor U a).sheafAdjunctionContinuous A
            (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).unit.app G)
          (proper_unit_app_isIso a A ha G)).hom =
      (@asIso _ _ _ _
          (((augmentationFunctor U a).sheafAdjunctionContinuous A
            (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).unit.app F)
          (proper_unit_app_isIso a A ha F)).hom ≫
        (properCartesianFunctor a A ⋙ properCartesianInverse a A).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ a_*` of proper hypercovering descent. -/
def properCartesianUnitIso (ha : IsProperHypercovering a) :
    𝟭 (Sheaf (spacesEtaleTopology X) A) ≅
      properCartesianFunctor a A ⋙ properCartesianInverse a A :=
  NatIso.ofComponents
    (fun F ↦
      @asIso _ _ _ _
        (((augmentationFunctor U a).sheafAdjunctionContinuous A
          (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).unit.app F)
        (proper_unit_app_isIso a A ha F))
    (fun f ↦ properCartesianUnitIso_naturality a A ha f)

/-- The component of `properCartesianUnitIso` at `F` is the adjunction unit. -/
theorem properCartesianUnitIso_hom_app (ha : IsProperHypercovering a)
    (F : Sheaf (spacesEtaleTopology X) A) :
    (properCartesianUnitIso a A ha).hom.app F =
      ((augmentationFunctor U a).sheafAdjunctionContinuous A
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).unit.app F :=
  sorry

/-- Naturality of the counit components of proper-hypercovering descent. -/
theorem properCartesianCounitIso_naturality (ha : IsProperHypercovering a)
    {F G : Cartesian U A} (f : F ⟶ G) :
    (properCartesianInverse a A ⋙ properCartesianFunctor a A).map f ≫
        ((cartesianProperty U A).isoMk
          (@asIso _ _ _ _
            (((augmentationFunctor U a).sheafAdjunctionContinuous A
              (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).counit.app G.obj)
            (proper_counit_app_isIso_of_isCartesian a A ha G.obj G.property))).hom =
      ((cartesianProperty U A).isoMk
          (@asIso _ _ _ _
            (((augmentationFunctor U a).sheafAdjunctionContinuous A
              (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).counit.app F.obj)
            (proper_counit_app_isIso_of_isCartesian a A ha F.obj F.property))).hom ≫
        (𝟭 (Cartesian U A)).map f :=
  sorry

/-- The counit isomorphism `a_* ⋙ a⁻¹ ≅ 𝟭` on cartesian sheaves. -/
def properCartesianCounitIso (ha : IsProperHypercovering a) :
    properCartesianInverse a A ⋙ properCartesianFunctor a A ≅ 𝟭 (Cartesian U A) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty U A).isoMk
        (@asIso _ _ _ _
          (((augmentationFunctor U a).sheafAdjunctionContinuous A
            (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).counit.app G.obj)
          (proper_counit_app_isIso_of_isCartesian a A ha G.obj G.property)))
    (fun f ↦ properCartesianCounitIso_naturality a A ha f)

/-- The component of `properCartesianCounitIso` at `G` is the adjunction counit on the
underlying sheaf. -/
theorem properCartesianCounitIso_hom_app_hom (ha : IsProperHypercovering a)
    (G : Cartesian U A) :
    ((properCartesianCounitIso a A ha).hom.app G).hom =
      ((augmentationFunctor U a).sheafAdjunctionContinuous A
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).counit.app G.obj :=
  sorry

/-- If `a` is a proper hypercovering of `X`, then `a⁻¹` implements an equivalence
between sheaves on `X_étale` and cartesian sheaves on `U_étale`, with quasi-inverse
`a_*`. -/
def properCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (spacesEtaleTopology X) A ≌ Cartesian U A :=
  CategoryTheory.Equivalence.mk (properCartesianFunctor a A) (properCartesianInverse a A)
    (properCartesianUnitIso a A ha) (properCartesianCounitIso a A ha)

/-- The forward functor of `properCartesianEquivalence` is `a⁻¹` corestricted to
cartesian sheaves. -/
theorem properCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (properCartesianEquivalence a A ha).functor = properCartesianFunctor a A :=
  sorry

/-- The inverse functor of `properCartesianEquivalence` is `a_*` on cartesian sheaves. -/
theorem properCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (properCartesianEquivalence a A ha).inverse = properCartesianInverse a A :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
