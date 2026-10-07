module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.RegularSurface

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped MonoidalCategory

noncomputable section

universe u

/- Lemma 54.3.4 (1): on the maximal-ideal blowup of a two-dimensional regular local
ring, the cohomology of every quasicoherent module vanishes in degrees at least two. -/
@[stacks 0AGS] #check
  (AlgebraicGeometry.IsBlowup.higherCohomology_isZero_of_maximalIdeal :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
      (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 2 ≤ p),
      IsZero (Scheme.Hom.cohomology f F p))

/- Lemma 54.3.4 (2): the first cohomology of the twist `𝒪_X(n)` on the
maximal-ideal blowup vanishes for every `n ≥ -1`. -/
@[stacks 0AGS] #check
  (AlgebraicGeometry.IsBlowup.twistCohomology_one_isZero_of_maximalIdeal :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
      (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (n : ℤ) (hn : -1 ≤ n),
      IsZero (Scheme.Hom.cohomology f
        (AlgebraicGeometry.IsBlowup.twistingSheaf
          (IsLocalRing.maximalIdeal A) f n) 1))

/- Lemma 54.3.4 (3): a quasicoherent module has vanishing first cohomology if
it or its degree-one twist is globally generated. -/
@[stacks 0AGS] #check
  (AlgebraicGeometry.IsBlowup.cohomology_one_isZero_of_globalGeneration :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
      (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (F : X.Modules) [F.IsQuasicoherent]
      (hF : SheafOfModules.IsGloballyGenerated F ∨
        SheafOfModules.IsGloballyGenerated
          (F ⊗ (AlgebraicGeometry.IsBlowup.twistingSheaf
            (IsLocalRing.maximalIdeal A) f 1))),
      IsZero (Scheme.Hom.cohomology f F 1))

/- Lemma 54.3.4 (4): degree-zero cohomology of `𝒪_X(n)` on the maximal-ideal
blowup is the ideal power `𝔪 ^ max 0 n`. -/
@[stacks 0AGS] #check
  (AlgebraicGeometry.IsBlowup.twistCohomology_zero_of_maximalIdeal :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
      (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (n : ℤ),
      IsIsomorphic
        (Scheme.Hom.cohomology f
          (AlgebraicGeometry.IsBlowup.twistingSheaf
            (IsLocalRing.maximalIdeal A) f n) 0)
        (ModuleCat.of A ((IsLocalRing.maximalIdeal A) ^ n.toNat : Ideal A)))

/- Lemma 54.3.4 (5): for a negative twist `n`, the first cohomology has
`A`-module length `Nat.choose n.natAbs 2 = -n(-n - 1) / 2`. -/
@[stacks 0AGS] #check
  (AlgebraicGeometry.IsBlowup.twistCohomology_one_length_of_neg :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
      (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
      (n : ℤ) (hn : n < 0),
      Module.length A
        (Scheme.Hom.cohomology f
          (AlgebraicGeometry.IsBlowup.twistingSheaf
            (IsLocalRing.maximalIdeal A) f n) 1) =
        (n.natAbs.choose 2 : ℕ∞))
