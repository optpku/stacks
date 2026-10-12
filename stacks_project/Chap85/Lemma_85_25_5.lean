/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_25_1_Forget
public import stacks_project.Chap85.Lemma_85_25_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_25_3
public import stacks_project.Chap85.Lemma_85_25_5_Equivalence

/-!
# Lemma 85.25.5

If `a : U ⟶ X` is a proper hypercovering in `LCCat`, then the exact inverse
image `a⁻¹` of the Lemma 85.2.8 Zariski augmentation induces an equivalence
`D⁺(X) ≌ D_A⁺(U_Zar)`, with quasi-inverse `Ra_*`, where `A` is the weak Serre
subcategory of cartesian abelian sheaves on `U_Zar`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.SimplicialObject Opposite
open scoped Simplicial

noncomputable section

universe u

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasSheafify (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [∀ n : ℕ, HasSheafify
    (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋n⦌))) AddCommGrpCat.{u}]
variable [(augmentationPushforward (toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]

/-- The derived counit `Ra_* ⋙ a⁻¹ ⟶ 𝟭` is an isomorphism on objects of `D⁺` with
cartesian cohomology. -/
theorem plus_counit_app_isIso_of_cohomologyIn (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus
      (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))
    (h : DerivedCategory.Plus.cohomologyIn
      (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}) K) :
    IsIso ((plusDerivedAdjunction (toTopCatAugmentation a)).counit.app K) :=
  sorry

/-- Naturality of the unit components of the bounded-below cartesian derived
equivalence. -/
theorem plusCartesianUnitIso_naturality (ha : IsProperHypercovering a)
    {K L : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})} (f : K ⟶ L) :
    (𝟭 (DerivedCategory.Plus
          (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}))).map f ≫
        (@asIso _ _ _ _
          ((plusDerivedUnit (toTopCatAugmentation a)).app L)
          (plusDerivedUnit_app_isIso a ha L)).hom =
      (@asIso _ _ _ _
          ((plusDerivedUnit (toTopCatAugmentation a)).app K)
          (plusDerivedUnit_app_isIso a ha K)).hom ≫
        (plusInverseImageCartesian (toTopCatAugmentation a) ⋙
          plusDirectImageCartesian (toTopCatAugmentation a)).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ Ra_*` on `D⁺(X)`. -/
def plusCartesianUnitIso (ha : IsProperHypercovering a) :
    𝟭 (DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})) ≅
      plusInverseImageCartesian (toTopCatAugmentation a) ⋙
        plusDirectImageCartesian (toTopCatAugmentation a) :=
  NatIso.ofComponents
    (fun K ↦
      @asIso _ _ _ _
        ((plusDerivedUnit (toTopCatAugmentation a)).app K)
        (plusDerivedUnit_app_isIso a ha K))
    (fun f ↦ plusCartesianUnitIso_naturality a ha f)

/-- Naturality of the counit components of the bounded-below cartesian derived
equivalence. -/
theorem plusCartesianCounitIso_naturality (ha : IsProperHypercovering a)
    {F G : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u})} (f : F ⟶ G) :
    (plusDirectImageCartesian (toTopCatAugmentation a) ⋙
        plusInverseImageCartesian (toTopCatAugmentation a)).map f ≫
        ((DerivedCategory.Plus.cohomologyIn
            (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u})).isoMk
          (@asIso _ _ _ _
            ((plusDerivedAdjunction (toTopCatAugmentation a)).counit.app G.obj)
            (plus_counit_app_isIso_of_cohomologyIn a ha G.obj G.property))).hom =
      ((DerivedCategory.Plus.cohomologyIn
          (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u})).isoMk
        (@asIso _ _ _ _
          ((plusDerivedAdjunction (toTopCatAugmentation a)).counit.app F.obj)
          (plus_counit_app_isIso_of_cohomologyIn a ha F.obj F.property))).hom ≫
        (𝟭 (DerivedCategory.Plus.CohomologyIn
            (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}))).map f :=
  sorry

/-- The counit isomorphism `Ra_* ⋙ a⁻¹ ≅ 𝟭` on `D_A⁺(U_Zar)`. -/
def plusCartesianCounitIso (ha : IsProperHypercovering a) :
    plusDirectImageCartesian (toTopCatAugmentation a) ⋙
        plusInverseImageCartesian (toTopCatAugmentation a) ≅
      𝟭 (DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u})) :=
  NatIso.ofComponents
    (fun G ↦
      (DerivedCategory.Plus.cohomologyIn
          (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u})).isoMk
        (@asIso _ _ _ _
          ((plusDerivedAdjunction (toTopCatAugmentation a)).counit.app G.obj)
          (plus_counit_app_isIso_of_cohomologyIn a ha G.obj G.property)))
    (fun f ↦ plusCartesianCounitIso_naturality a ha f)

/-- Lemma 85.25.5. Let `U` be a simplicial object of `LCCat` and let `a : U ⟶ X`
be an augmentation. Let `A` denote the weak Serre subcategory of cartesian abelian
sheaves on `U_Zar`. If `a` is a proper hypercovering of `X`, then the functor
`a⁻¹` defines an equivalence
`DerivedCategory.Plus` of abelian sheaves on `X` with
`DerivedCategory.Plus.CohomologyIn` of `cartesianProperty` on `U_Zar`, with
quasi-inverse `Ra_*`, where `a` is the Lemma 85.2.8 Zariski augmentation
`augmentationMorphism (toTopCatAugmentation a)`. -/
@[stacks 0DAH]
def plusCartesianEquivalence (ha : IsProperHypercovering a) :
    DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}) :=
  CategoryTheory.Equivalence.mk
    (plusInverseImageCartesian (toTopCatAugmentation a))
    (plusDirectImageCartesian (toTopCatAugmentation a))
    (plusCartesianUnitIso a ha) (plusCartesianCounitIso a ha)

/-- The forward functor of `plusCartesianEquivalence` is `a⁻¹` corestricted to
objects with cartesian cohomology. -/
theorem plusCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (plusCartesianEquivalence a ha).functor =
      plusInverseImageCartesian (toTopCatAugmentation a) :=
  sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` on objects with
cartesian cohomology. -/
theorem plusCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (plusCartesianEquivalence a ha).inverse =
      plusDirectImageCartesian (toTopCatAugmentation a) :=
  sorry

end LCCat

end
