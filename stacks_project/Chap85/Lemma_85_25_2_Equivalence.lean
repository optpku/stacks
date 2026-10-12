/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap85.Lemma_85_25_1_Forget
public import stacks_project.Chap85.Lemma_85_25_2_Cartesian
public import stacks_project.Chap85.Lemma_85_25_2_Hypercovering

/-!
# Descent equivalence for proper hypercoverings in `LCCat`

If `a : U ⟶ X` is a proper hypercovering, then `a⁻¹` identifies sheaves on `X`
with cartesian sheaves on `U_Zar`, with quasi-inverse `a_*`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace LCCat

section CoefficientGeneric

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable (A : Type (u + 1)) [Category.{u} A]
variable [HasWeakSheafify (Opens.grothendieckTopology X.obj) A]
variable [HasWeakSheafify (zariskiTopology (constSpace X.obj)) A]
variable [HasWeakSheafify (zariskiTopology (forgetToTop.obj U)) A]
variable [∀ n : ℕ,
    HasWeakSheafify (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋n⦌))) A]
variable [∀ P : (zariskiSite (constSpace X.obj))ᵒᵖ ⥤ A,
    (zariskiMap (toTopCatAugmentation a)).op.HasLeftKanExtension P]
variable [∀ P : (zariskiSite (constSpace X.obj))ᵒᵖ ⥤ A,
    (constProjection X.obj).op.HasPointwiseRightKanExtension P]
variable [HasOpensMapLeftKanExtension (forgetToTop.obj U) A]

/-- Inverse image `a⁻¹` along a proper hypercovering is full. -/
theorem properInverseImage_full (ha : IsProperHypercovering a) :
    (inverseImage (toTopCatAugmentation a) A).Full :=
  sorry

/-- Inverse image `a⁻¹` along a proper hypercovering is faithful. -/
theorem properInverseImage_faithful (ha : IsProperHypercovering a) :
    (inverseImage (toTopCatAugmentation a) A).Faithful :=
  sorry

/-- Inverse image `a⁻¹` along a proper hypercovering is fully faithful. -/
def properInverseImage_fullyFaithful (ha : IsProperHypercovering a) :
    (inverseImage (toTopCatAugmentation a) A).FullyFaithful :=
  @FullyFaithful.ofFullyFaithful _ _ _ _ (inverseImage (toTopCatAugmentation a) A)
    (properInverseImage_full a A ha) (properInverseImage_faithful a A ha)

/-- The unit of `a⁻¹ ⊣ a_*` is an isomorphism along a proper hypercovering. -/
theorem proper_unit_app_isIso (ha : IsProperHypercovering a)
    (F : Sheaf (Opens.grothendieckTopology X.obj) A) :
    IsIso ((inverseImageAdjunction (toTopCatAugmentation a) A).unit.app F) :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism precisely on cartesian sheaves. -/
theorem proper_counit_app_isIso_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) A) :
    IsIso ((inverseImageAdjunction (toTopCatAugmentation a) A).counit.app G) ↔
      IsCartesian (forgetToTop.obj U) A G :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism on a cartesian sheaf. -/
theorem proper_counit_app_isIso_of_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) A)
    (h : IsCartesian (forgetToTop.obj U) A G) :
    IsIso ((inverseImageAdjunction (toTopCatAugmentation a) A).counit.app G) :=
  sorry

/-- A sheaf on `U_Zar` lies in the essential image of `a⁻¹` if and only if it is
cartesian. -/
theorem proper_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) A) :
    (inverseImage (toTopCatAugmentation a) A).essImage G ↔
      IsCartesian (forgetToTop.obj U) A G :=
  sorry

/-- The functor `a⁻¹` corestricted to cartesian sheaves on `U_Zar`. -/
def properCartesianFunctor :
    Sheaf (Opens.grothendieckTopology X.obj) A ⥤ Cartesian (forgetToTop.obj U) A :=
  (cartesianProperty (forgetToTop.obj U) A).lift
    (inverseImage (toTopCatAugmentation a) A) fun F ↦
      inverseImage_isCartesian (toTopCatAugmentation a) A F

/-- On objects, `properCartesianFunctor` is inverse image along the Zariski
augmentation. -/
theorem properCartesianFunctor_obj (F : Sheaf (Opens.grothendieckTopology X.obj) A) :
    ((properCartesianFunctor a A).obj F).obj =
      (inverseImage (toTopCatAugmentation a) A).obj F :=
  sorry

/-- The functor sending a cartesian sheaf on `U_Zar` to `a_*` of its underlying sheaf. -/
def properCartesianInverse :
    Cartesian (forgetToTop.obj U) A ⥤ Sheaf (Opens.grothendieckTopology X.obj) A :=
  (cartesianProperty (forgetToTop.obj U) A).ι ⋙ directImage (toTopCatAugmentation a) A

/-- On objects, `properCartesianInverse` is direct image along the Zariski augmentation. -/
theorem properCartesianInverse_obj (G : Cartesian (forgetToTop.obj U) A) :
    (properCartesianInverse a A).obj G =
      (directImage (toTopCatAugmentation a) A).obj G.obj :=
  sorry

/-- Naturality of the unit components of proper-hypercovering descent. -/
theorem properCartesianUnitIso_naturality (ha : IsProperHypercovering a)
    {F G : Sheaf (Opens.grothendieckTopology X.obj) A} (f : F ⟶ G) :
    (𝟭 (Sheaf (Opens.grothendieckTopology X.obj) A)).map f ≫
        (@asIso _ _ _ _
          ((inverseImageAdjunction (toTopCatAugmentation a) A).unit.app G)
          (proper_unit_app_isIso a A ha G)).hom =
      (@asIso _ _ _ _
          ((inverseImageAdjunction (toTopCatAugmentation a) A).unit.app F)
          (proper_unit_app_isIso a A ha F)).hom ≫
        (properCartesianFunctor a A ⋙ properCartesianInverse a A).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ a_*` of proper hypercovering descent. -/
def properCartesianUnitIso (ha : IsProperHypercovering a) :
    𝟭 (Sheaf (Opens.grothendieckTopology X.obj) A) ≅
      properCartesianFunctor a A ⋙ properCartesianInverse a A :=
  NatIso.ofComponents
    (fun F ↦
      @asIso _ _ _ _
        ((inverseImageAdjunction (toTopCatAugmentation a) A).unit.app F)
        (proper_unit_app_isIso a A ha F))
    (fun f ↦ properCartesianUnitIso_naturality a A ha f)

/-- The component of `properCartesianUnitIso` at `F` is the adjunction unit. -/
theorem properCartesianUnitIso_hom_app (ha : IsProperHypercovering a)
    (F : Sheaf (Opens.grothendieckTopology X.obj) A) :
    (properCartesianUnitIso a A ha).hom.app F =
      (inverseImageAdjunction (toTopCatAugmentation a) A).unit.app F :=
  sorry

/-- Naturality of the counit components of proper-hypercovering descent. -/
theorem properCartesianCounitIso_naturality (ha : IsProperHypercovering a)
    {F G : Cartesian (forgetToTop.obj U) A} (f : F ⟶ G) :
    (properCartesianInverse a A ⋙ properCartesianFunctor a A).map f ≫
        ((cartesianProperty (forgetToTop.obj U) A).isoMk
          (@asIso _ _ _ _
            ((inverseImageAdjunction (toTopCatAugmentation a) A).counit.app G.obj)
            (proper_counit_app_isIso_of_isCartesian a A ha G.obj G.property))).hom =
      ((cartesianProperty (forgetToTop.obj U) A).isoMk
          (@asIso _ _ _ _
            ((inverseImageAdjunction (toTopCatAugmentation a) A).counit.app F.obj)
            (proper_counit_app_isIso_of_isCartesian a A ha F.obj F.property))).hom ≫
        (𝟭 (Cartesian (forgetToTop.obj U) A)).map f :=
  sorry

/-- The counit isomorphism `a_* ⋙ a⁻¹ ≅ 𝟭` on cartesian sheaves. -/
def properCartesianCounitIso (ha : IsProperHypercovering a) :
    properCartesianInverse a A ⋙ properCartesianFunctor a A ≅
      𝟭 (Cartesian (forgetToTop.obj U) A) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty (forgetToTop.obj U) A).isoMk
        (@asIso _ _ _ _
          ((inverseImageAdjunction (toTopCatAugmentation a) A).counit.app G.obj)
          (proper_counit_app_isIso_of_isCartesian a A ha G.obj G.property)))
    (fun f ↦ properCartesianCounitIso_naturality a A ha f)

/-- The component of `properCartesianCounitIso` at `G` is the adjunction counit on the
underlying sheaf. -/
theorem properCartesianCounitIso_hom_app_hom (ha : IsProperHypercovering a)
    (G : Cartesian (forgetToTop.obj U) A) :
    ((properCartesianCounitIso a A ha).hom.app G).hom =
      (inverseImageAdjunction (toTopCatAugmentation a) A).counit.app G.obj :=
  sorry

/-- If `a` is a proper hypercovering of `X`, then `a⁻¹` implements an equivalence
between sheaves on `X` and cartesian sheaves on `U_Zar`, with quasi-inverse `a_*`. -/
def properCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (Opens.grothendieckTopology X.obj) A ≌ Cartesian (forgetToTop.obj U) A :=
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

end CoefficientGeneric

end LCCat

end
