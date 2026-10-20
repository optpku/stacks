module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.CartesianDerived
public import ReasLib.Topology.Sheaves.Simplicial.ProperDescent.Derived

/-!
# Bounded-below cartesian derived descent for proper hypercoverings

A proper hypercovering of Hausdorff locally compact spaces induces an equivalence
between bounded-below derived abelian sheaves on the base and those with cartesian
cohomology on its simplicial Zariski site. Its functors are the canonical derived
augmentation inverse and direct images.
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
    (fun f ↦ (plusDerivedUnit (toTopCatAugmentation a)).naturality f)

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
    (fun f ↦ by
      apply CategoryTheory.ObjectProperty.hom_ext
      exact (plusDerivedAdjunction (toTopCatAugmentation a)).counit.naturality f.hom)

/-- A proper hypercovering of Hausdorff locally compact spaces induces an
 equivalence from bounded-below derived abelian sheaves on the base to those with
 cartesian cohomology on the simplicial Zariski site. The forward functor is
 canonical inverse image and the quasi-inverse is canonical derived direct image. -/
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
  rfl

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` on objects with
cartesian cohomology. -/
theorem plusCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (plusCartesianEquivalence a ha).inverse =
      plusDirectImageCartesian (toTopCatAugmentation a) :=
  rfl

end LCCat

end
