/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.FittingIso
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Obstruction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.IsoClass
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.IsoClass
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.NaiveComparison

/-!
# The cotangent torsor of first-order deformation classes

Canonical difference of geometric solution classes defines their simply transitive
Ext¹ action. A solution supplies nonemptiness and a normalized based chart.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits DerivedCategory
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening hiding Solution
open RingedSite.ToposHom
open SheafOfModules.RingedSite.CotangentComplex (coeffSingle extOneTruncEquiv)
open scoped DerivedExt RingedSite.ToposHom SheafOfModules.RingedSite

namespace RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]

-- Local instance justification (defeq pin): pin Q, singleFunctor, and Ext to the reducible standard derived category of the site-presented module category.
attribute [local instance] moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): pin ModuleDerived and site-presented Ext to the same standard derived-category localization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {O : Sheaf JC CommRingCat.{u}}
variable {OB OB' : Sheaf JD CommRingCat.{u}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

/-- Two solutions are related iff a fitting isomorphism exists. -/
theorem isoSetoid_rel (S₁ S₂ : Solution t f G c) :
    Solution.isoSetoid t f G c S₁ S₂ ↔ Nonempty (SolutionIso S₁ S₂) :=
  sorry

/-- A fitting isomorphism identifies isomorphism classes. -/
theorem isoClassMk_eq_of_iso {S₁ S₂ : Solution t f G c} (φ : SolutionIso S₁ S₂) :
    Solution.isoClassMk t f G c S₁ = Solution.isoClassMk t f G c S₂ :=
  sorry

/-- Forgetting commutativity of inverse image along `f` recovers the bundled ring-valued
inverse image. -/
private def inverseImageCommRing_ring (R : Sheaf JD CommRingCat.{u}) :
    ringSheaf JC ((f.toTopos.commRingInverseImage).obj R) ≅
      f.toTopos.ringInverseImage.obj (ringSheaf JD R) :=
  Iso.refl _

/-- The inverse-image structure map of a two-site solution, as a commutative ring-sheaf
morphism. -/
@[no_expose] def fromInverseImageComm (S : Solution t f G c) :
    (f.toTopos.commRingInverseImage).obj OB' ⟶ S.middle :=
  InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimage
    ((inverseImageCommRing_ring f OB').hom ≫ S.fromInverseImage)

/-- Convert a two-site solution to the same-site solution of the pulled thickening. -/
def toSameSite (S : Solution t f G c) :
    SheafOfModules.RingedSite.FirstOrderThickening.Solution
      (pulledThickening t f) (pulled_isFirstOrderThickening t f).isSquareZero
      (commRingStructureMap f) G (coeffSameSite t f G c) :=
  { middle := S.middle
    proj := S.π
    structureMap := fromInverseImageComm t f G c S
    proj_locallySurjective := S.isFirstOrder.isLocallySurjective
    proj_squareZero := S.isFirstOrder.isSquareZero
    proj_quotient_isIso := @KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ S.π _
      S.isFirstOrder.isLocallySurjective
    commutes := sorry
    kernelIso := S.kernelIso
    induces_c := sorry }

/-- Convert a same-site solution of the pulled thickening to a two-site solution. -/
@[no_expose] def fromSameSite
    (S : SheafOfModules.RingedSite.FirstOrderThickening.Solution
      (pulledThickening t f) (pulled_isFirstOrderThickening t f).isSquareZero
      (commRingStructureMap f) G (coeffSameSite t f G c)) :
    Solution t f G c :=
  Solution.of t f G c S.middle S.proj
    (isFirstOrder :=
      { isLocallySurjective := S.proj_locallySurjective
        isSquareZero := S.proj_squareZero })
    ((inverseImageCommRing_ring f OB').inv ≫ ringSheafMap S.structureMap) sorry
    ((SheafOfModules.RingedSite.FirstOrderThickening.Solution.idealTargetIso S).trans
      S.kernelIso) sorry

/-- Isomorphism classes of two-site solutions are identified with same-site classes of the
pulled thickening. -/
def isoClassCongr :
    SheafOfModules.RingedSite.FirstOrderThickening.Solution.IsoClass
      (pulledThickening t f) (pulled_isFirstOrderThickening t f).isSquareZero
      (commRingStructureMap f) G (coeffSameSite t f G c) ≃
      Solution.IsoClass t f G c where
  toFun := Quotient.map (fromSameSite t f G c) sorry
  invFun := Quotient.map (toSameSite t f G c) sorry
  left_inv := sorry
  right_inv := sorry

/-- The difference of two geometric deformation classes is their same-site Ext¹ difference. -/
def naiveDifference (p q : Solution.IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G) :=
  SheafOfModules.RingedSite.FirstOrderThickening.Solution.vsub
    ((isoClassCongr t f G c).symm p) ((isoClassCongr t f G c).symm q)

/-- A deformation class has zero difference from itself. -/
theorem naiveDifference_self (p : Solution.IsoClass t f G c) :
    naiveDifference t f G c p p = 0 := sorry

/-- Differences of deformation classes satisfy the additive cocycle identity. -/
theorem naiveDifference_add (p q r : Solution.IsoClass t f G c) :
    naiveDifference t f G c p q + naiveDifference t f G c q r =
      naiveDifference t f G c p r := sorry

/-- Difference from a fixed geometric class is a bijection onto naive cotangent Ext¹. -/
theorem naiveDifference_bijective (p : Solution.IsoClass t f G c) :
    Function.Bijective (fun q ↦ naiveDifference t f G c q p) := sorry

/-- The based naive chart is the specified inverse of difference from the basepoint class. -/
def isoClassNaiveEquiv (S0 : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G) ≃ Solution.IsoClass t f G c :=
  (Equiv.ofBijective (fun q ↦ naiveDifference t f G c q (Solution.isoClassMk t f G c S0))
    (naiveDifference_bijective t f G c (Solution.isoClassMk t f G c S0))).symm

/-- The class in the based chart has the prescribed difference from the basepoint. -/
theorem isoClassNaiveEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G)) :
    naiveDifference t f G c (isoClassNaiveEquiv t f G c S0 ξ)
      (Solution.isoClassMk t f G c S0) = ξ := sorry

/-- The based naive chart sends zero to the basepoint class. -/
theorem isoClassNaiveEquiv_zero (S0 : Solution t f G c) :
    isoClassNaiveEquiv t f G c S0 0 = Solution.isoClassMk t f G c S0 := sorry

/-- The inverse based naive chart is difference from the basepoint class. -/
theorem isoClassNaiveEquiv_symm_apply (S0 : Solution t f G c)
    (p : Solution.IsoClass t f G c) :
    (isoClassNaiveEquiv t f G c S0).symm p =
      naiveDifference t f G c p (Solution.isoClassMk t f G c S0) := sorry

/-- Derived cotangent difference is naive difference transported through good truncation. -/
def derivedVSub (p q : Solution.IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G) :=
  extOneTruncEquiv (commRingStructureMap f) G (naiveDifference t f G c p q)

/-- Translation by a derived Ext¹ class is the specified inverse of difference. -/
def derivedVAdd
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G))
    (p : Solution.IsoClass t f G c) : Solution.IsoClass t f G c :=
  (Equiv.ofBijective (fun q ↦ naiveDifference t f G c q p)
    (naiveDifference_bijective t f G c p)).symm
      ((extOneTruncEquiv (commRingStructureMap f) G).symm ξ)

/-- Translation is uniquely characterized by its derived cotangent difference. -/
theorem derivedVAdd_spec
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G))
    (p q : Solution.IsoClass t f G c) :
    derivedVAdd t f G c ξ p = q ↔ derivedVSub t f G c q p = ξ := sorry

/-- Geometric deformation classes form a torsor under derived cotangent Ext¹ whenever
there is a solution; the solution supplies only nonemptiness. -/
@[reducible] def derivedAddTorsor (S0 : Solution t f G c) :
    AddTorsor
      (Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G))
      (Solution.IsoClass t f G c) where
  vadd := derivedVAdd t f G c
  vsub := derivedVSub t f G c
  nonempty := ⟨Solution.isoClassMk t f G c S0⟩
  zero_vadd := sorry
  add_vadd := sorry
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- The based derived chart is the naive chart transported through good truncation. -/
def isoClassDerivedEquiv (S0 : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G) ≃
      Solution.IsoClass t f G c :=
  (extOneTruncEquiv (commRingStructureMap f) G).symm.toEquiv.trans (isoClassNaiveEquiv t f G c S0)

/-- The based chart sends a derived Ext¹ class to the translate of the basepoint. -/
theorem isoClassDerivedEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G)) :
    isoClassDerivedEquiv t f G c S0 ξ =
      isoClassNaiveEquiv t f G c S0 ((extOneTruncEquiv (commRingStructureMap f) G).symm ξ) :=
  sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassDerivedEquiv_zero (S0 : Solution t f G c) :
    isoClassDerivedEquiv t f G c S0 0 = Solution.isoClassMk t f G c S0 :=
  sorry

/-- The inverse chart is the naive torsor subtraction, transported along
`extOneTruncEquiv`. -/
theorem isoClassDerivedEquiv_symm_apply (S0 : Solution t f G c)
    (p : Solution.IsoClass t f G c) :
    (isoClassDerivedEquiv t f G c S0).symm p =
      extOneTruncEquiv (commRingStructureMap f) G ((isoClassNaiveEquiv t f G c S0).symm p) :=
  sorry

end RingedSite.FirstOrderThickening
