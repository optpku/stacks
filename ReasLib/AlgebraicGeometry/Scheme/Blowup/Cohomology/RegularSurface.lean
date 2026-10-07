module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- Higher cohomology vanishes on the maximal-ideal blowup of a two-dimensional regular local ring. -/
theorem higherCohomology_isZero_of_maximalIdeal
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 2 ≤ p) :
    IsZero (Scheme.Hom.cohomology f F p) := sorry

/-- First cohomology of the integral twist vanishes for every index at least `-1`. -/
theorem twistCohomology_one_isZero_of_maximalIdeal
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℤ) (hn : -1 ≤ n) :
    IsZero (Scheme.Hom.cohomology f
      (twistingSheaf (IsLocalRing.maximalIdeal A) f n) 1) := sorry

/-- First cohomology vanishes when a quasicoherent module or its degree-one twist is globally generated. -/
theorem cohomology_one_isZero_of_globalGeneration
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : SheafOfModules.IsGloballyGenerated F ∨
        SheafOfModules.IsGloballyGenerated
          (F ⊗ (twistingSheaf (IsLocalRing.maximalIdeal A) f 1))) :
    IsZero (Scheme.Hom.cohomology f F 1) := sorry

/-- Degree-zero cohomology of the integral twist is the corresponding maximal-ideal power. -/
theorem twistCohomology_zero_of_maximalIdeal
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℤ) :
    IsIsomorphic
      (Scheme.Hom.cohomology f
        (twistingSheaf (IsLocalRing.maximalIdeal A) f n) 0)
      (ModuleCat.of A ((IsLocalRing.maximalIdeal A) ^ n.toNat : Ideal A)) := sorry

/-- The length of first cohomology of a negative integral twist is the corresponding binomial coefficient. -/
theorem twistCohomology_one_length_of_neg
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℤ) (hn : n < 0) :
    Module.length A
      (Scheme.Hom.cohomology f
        (twistingSheaf (IsLocalRing.maximalIdeal A) f n) 1) =
      (n.natAbs.choose 2 : ℕ∞) := sorry

end AlgebraicGeometry.IsBlowup
