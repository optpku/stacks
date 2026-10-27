/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering

/-!
# Descent equivalence for fppf hypercoverings on the spaces-étale site

If `a : U ⟶ X` is an fppf hypercovering, then `a⁻¹` is fully faithful with essential
image the cartesian sheaves on `U_étale`, and `a_*` is a quasi-inverse.
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

/-- The adjunction `a⁻¹ ⊣ a_*` presented by the continuous functor `augmentationFunctor a`. -/
def sheafLocalizationAdjunction :
    inverseImage U A a ⊣ directImage U A a :=
  (augmentationFunctor U a).sheafAdjunctionContinuous A
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U)

/-- `sheafLocalizationAdjunction` is `sheafAdjunctionContinuous` of `augmentationFunctor a`. -/
theorem sheafLocalizationAdjunction_eq :
    sheafLocalizationAdjunction a A =
      (augmentationFunctor U a).sheafAdjunctionContinuous A
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U) :=
  sorry

/-- Inverse image `a⁻¹` along an fppf hypercovering is full. -/
theorem inverseImage_full (ha : IsFppfHypercovering a) : (inverseImage U A a).Full :=
  sorry

/-- Inverse image `a⁻¹` along an fppf hypercovering is faithful. -/
theorem inverseImage_faithful (ha : IsFppfHypercovering a) : (inverseImage U A a).Faithful :=
  sorry

/-- Inverse image `a⁻¹` along an fppf hypercovering is fully faithful. -/
def inverseImage_fullyFaithful (ha : IsFppfHypercovering a) :
    (inverseImage U A a).FullyFaithful :=
  @FullyFaithful.ofFullyFaithful _ _ _ _ (inverseImage U A a)
    (inverseImage_full a A ha) (inverseImage_faithful a A ha)

/-- The unit of `a⁻¹ ⊣ a_*` is an isomorphism. -/
theorem _root_.StacksProject.Chap85.Lemma_85_33_2.unit_app_isIso
    (ha : IsFppfHypercovering a) (F : Sheaf (spacesEtaleTopology X) A) :
    IsIso ((sheafLocalizationAdjunction a A).unit.app F) :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism precisely on cartesian sheaves. -/
theorem counit_app_isIso_iff_isCartesian (ha : IsFppfHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) A) :
    IsIso ((sheafLocalizationAdjunction a A).counit.app G) ↔ IsCartesian U A G :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism on a cartesian sheaf. -/
theorem counit_app_isIso_of_isCartesian (ha : IsFppfHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) A) (h : IsCartesian U A G) :
    IsIso ((sheafLocalizationAdjunction a A).counit.app G) :=
  sorry

/-- A sheaf on `U_étale` lies in the essential image of `a⁻¹` if and only if it is cartesian. -/
theorem mem_essImage_iff_isCartesian (ha : IsFppfHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) A) :
    (inverseImage U A a).essImage G ↔ IsCartesian U A G :=
  sorry

/-- The functor `a⁻¹` corestricted to cartesian sheaves on `U_étale`. -/
def cartesianFunctor : Sheaf (spacesEtaleTopology X) A ⥤ Cartesian U A :=
  (cartesianProperty U A).lift (inverseImage U A a) fun F ↦ inverseImage_isCartesian U A a F

/-- On objects, `cartesianFunctor` is inverse image along the spaces-étale augmentation. -/
theorem cartesianFunctor_obj (F : Sheaf (spacesEtaleTopology X) A) :
    ((cartesianFunctor a A).obj F).obj = (inverseImage U A a).obj F :=
  sorry

/-- The functor sending a cartesian sheaf on `U_étale` to `a_*` of its underlying sheaf. -/
def cartesianInverse : Cartesian U A ⥤ Sheaf (spacesEtaleTopology X) A :=
  (cartesianProperty U A).ι ⋙ directImage U A a

/-- On objects, `cartesianInverse` is direct image along the spaces-étale augmentation. -/
theorem cartesianInverse_obj (G : Cartesian U A) :
    (cartesianInverse a A).obj G = (directImage U A a).obj G.obj :=
  sorry

/-- Naturality of the unit components of hypercovering descent. -/
theorem cartesianUnitIso_naturality (ha : IsFppfHypercovering a)
    {F G : Sheaf (spacesEtaleTopology X) A} (f : F ⟶ G) :
    (𝟭 (Sheaf (spacesEtaleTopology X) A)).map f ≫
        (@asIso _ _ _ _ ((sheafLocalizationAdjunction a A).unit.app G)
          (StacksProject.Chap85.Lemma_85_33_2.unit_app_isIso a A ha G)).hom =
      (@asIso _ _ _ _ ((sheafLocalizationAdjunction a A).unit.app F)
          (StacksProject.Chap85.Lemma_85_33_2.unit_app_isIso a A ha F)).hom ≫
        (cartesianFunctor a A ⋙ cartesianInverse a A).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ a_*` of fppf hypercovering descent. -/
def cartesianUnitIso (ha : IsFppfHypercovering a) :
    𝟭 (Sheaf (spacesEtaleTopology X) A) ≅ cartesianFunctor a A ⋙ cartesianInverse a A :=
  NatIso.ofComponents
    (fun F ↦
      @asIso _ _ _ _ ((sheafLocalizationAdjunction a A).unit.app F)
        (StacksProject.Chap85.Lemma_85_33_2.unit_app_isIso a A ha F))
    (fun f ↦ cartesianUnitIso_naturality a A ha f)

/-- The component of `cartesianUnitIso` at `F` is the adjunction unit. -/
theorem cartesianUnitIso_hom_app (ha : IsFppfHypercovering a)
    (F : Sheaf (spacesEtaleTopology X) A) :
    (cartesianUnitIso a A ha).hom.app F =
      (sheafLocalizationAdjunction a A).unit.app F :=
  sorry

/-- Naturality of the counit components of hypercovering descent. -/
theorem cartesianCounitIso_naturality (ha : IsFppfHypercovering a)
    {F G : Cartesian U A} (f : F ⟶ G) :
    (cartesianInverse a A ⋙ cartesianFunctor a A).map f ≫
        ((cartesianProperty U A).isoMk
          (@asIso _ _ _ _ ((sheafLocalizationAdjunction a A).counit.app G.obj)
            (counit_app_isIso_of_isCartesian a A ha G.obj G.property))).hom =
      ((cartesianProperty U A).isoMk
          (@asIso _ _ _ _ ((sheafLocalizationAdjunction a A).counit.app F.obj)
            (counit_app_isIso_of_isCartesian a A ha F.obj F.property))).hom ≫
        (𝟭 (Cartesian U A)).map f :=
  sorry

/-- The counit isomorphism `a_* ⋙ a⁻¹ ≅ 𝟭` on cartesian sheaves. -/
def cartesianCounitIso (ha : IsFppfHypercovering a) :
    cartesianInverse a A ⋙ cartesianFunctor a A ≅ 𝟭 (Cartesian U A) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty U A).isoMk
        (@asIso _ _ _ _ ((sheafLocalizationAdjunction a A).counit.app G.obj)
          (counit_app_isIso_of_isCartesian a A ha G.obj G.property)))
    (fun f ↦ cartesianCounitIso_naturality a A ha f)

/-- The component of `cartesianCounitIso` at `G` is the adjunction counit on the underlying
sheaf. -/
theorem cartesianCounitIso_hom_app_hom (ha : IsFppfHypercovering a) (G : Cartesian U A) :
    ((cartesianCounitIso a A ha).hom.app G).hom =
      (sheafLocalizationAdjunction a A).counit.app G.obj :=
  sorry

/-- If `a` is an fppf hypercovering of `X`, then `a⁻¹` implements an equivalence between
sheaves on `X_étale` and cartesian sheaves on `U_étale`, with quasi-inverse `a_*`. -/
def cartesianEquivalence (ha : IsFppfHypercovering a) :
    Sheaf (spacesEtaleTopology X) A ≌ Cartesian U A :=
  CategoryTheory.Equivalence.mk (cartesianFunctor a A) (cartesianInverse a A)
    (cartesianUnitIso a A ha) (cartesianCounitIso a A ha)

/-- The forward functor of `cartesianEquivalence` is `a⁻¹` corestricted to cartesian sheaves. -/
theorem cartesianEquivalence_functor (ha : IsFppfHypercovering a) :
    (cartesianEquivalence a A ha).functor = cartesianFunctor a A :=
  sorry

/-- The inverse functor of `cartesianEquivalence` is `a_*` on cartesian sheaves. -/
theorem cartesianEquivalence_inverse (ha : IsFppfHypercovering a) :
    (cartesianEquivalence a A ha).inverse = cartesianInverse a A :=
  sorry

/-- Opposite of `augmentationFunctor a` admits left Kan extensions of abelian presheaves in
universe `u + 1`. -/
instance augmentationFunctor_op_hasLeftKanExtension_addCommGrp
    (P : (spacesEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (augmentationFunctor U a).op.HasLeftKanExtension P :=
  sorry

/-- Inverse image of `spacesEtaleAugmentation a` on sheaves of types is `inverseImage`. -/
theorem inverseImage_eq_spacesEtaleAugmentation :
    inverseImage U (Type (u + 1)) a = (spacesEtaleAugmentation U a)⁻¹ :=
  sorry

/-- Direct image of `spacesEtaleAugmentation a` on sheaves of types is `directImage`. -/
theorem directImage_eq_spacesEtaleAugmentation :
    directImage U (Type (u + 1)) a = (spacesEtaleAugmentation U a)_* :=
  sorry

/-- Sheaves of abelian groups in universe `u + 1` on the total spaces-étale site admit
sheafification. -/
instance hasSheafify_spacesEtaleTotalTopology_addCommGrpCat :
    HasSheafify (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
