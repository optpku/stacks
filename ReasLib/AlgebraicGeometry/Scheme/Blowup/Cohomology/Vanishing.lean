/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.AdicSections
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.AssociatedGraded
public import ReasLib.Algebra.Module.ProjectiveFactorIdeal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct
noncomputable section
universe u

namespace AlgebraicGeometry.IsBlowup

/-- Top-degree cohomology of a sufficiently positive quotient-module twist vanishes. -/
theorem topTwistCohomology_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : 1 ≤ associatedGradedFiberDimension I)
    (hq : (associatedGradedUniformityThreshold I : ℤ) ≤ q) :
    IsZero (Scheme.Hom.cohomology p (quotientModuleTwist I p M q)
      (associatedGradedFiberDimension I)) := sorry

/-- Cohomology one degree below the top vanishes for a sufficiently positive quotient-module twist. -/
theorem penultimateTwistCohomology_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : 2 ≤ associatedGradedFiberDimension I)
    (hq : (associatedGradedUniformityThreshold I : ℤ) ≤ q) :
    IsZero (Scheme.Hom.cohomology p (quotientModuleTwist I p M q)
      (associatedGradedFiberDimension I - 1)) := sorry

/-- In an intermediate positive degree, the canonical twist transition induces the zero map on cohomology. -/
theorem twistTransition_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (i : ℕ) (q : ℤ) (hi : 0 < i)
    (hid : i < associatedGradedFiberDimension I - 1)
    (hq : (associatedGradedUniformityThreshold I : ℤ) +
      (((associatedGradedFiberDimension I - 1 - i) * c : ℕ) : ℤ) ≤ q) :
    (Scheme.Hom.cohomologyFunctor p i).map
      (canonicalTwistTransition I p M q
        ((associatedGradedFiberDimension I - 1 - i) * c)) = 0 := sorry

/-- The canonical adic tensor-section map is surjective in dimension at most one. -/
theorem adicSection_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : associatedGradedFiberDimension I ≤ 1)
    (hq : (associatedGradedUniformityThreshold I : ℤ) ≤ q) :
    Function.Surjective (canonicalAdicTensorSectionMap I p M q).hom := sorry

/-- The degree-zero transition has image contained in the canonical adic-section image in dimension greater than one. -/
theorem twistTransition_range_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : 1 < associatedGradedFiberDimension I)
    (hq : (associatedGradedUniformityThreshold I : ℤ) +
      (((associatedGradedFiberDimension I - 1) * c : ℕ) : ℤ) ≤ q) :
    LinearMap.range ((Scheme.Hom.cohomologyFunctor p 0).map
      (canonicalTwistTransition I p M q
        ((associatedGradedFiberDimension I - 1) * c))).hom ≤
      LinearMap.range (canonicalAdicTensorSectionMap I p M
        (q - (((associatedGradedFiberDimension I - 1) * c : ℕ) : ℤ))).hom := sorry

end AlgebraicGeometry.IsBlowup
