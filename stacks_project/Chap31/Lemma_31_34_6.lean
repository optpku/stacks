/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Denominator
import StacksCheckRecall

open CategoryTheory

noncomputable section

universe u

/- The complement of the denominator ideal is the maximal open locus on which
the meromorphic section is regular. -/
#check
  (AlgebraicGeometry.Scheme.IdealSheafData.openComplement_isGreatest_regularAt_of_eq_denominatorIdeal :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (I : X.IdealSheafData) (ℒ : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (_ : I.toSubobject = AlgebraicGeometry.Scheme.denominatorIdealSheaf ℒ s),
      IsGreatest
        {U : X.Opens |
          ∀ x : X, x ∈ U →
            AlgebraicGeometry.LocallyRingedSpace.MeromorphicSection.IsRegularAt s x}
        I.openComplement)

/- Lemma 31.34.6 (1): the blowup of the denominator ideal of a regular
meromorphic section on a locally Noetherian scheme is admissible over the
maximal open locus where the section is regular. -/
@[stacks 0ESL] #check
  (AlgebraicGeometry.Blowup.isAdmissible_denominatorIdeal :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.IsLocallyNoetherian X]
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (_ : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
      (I : X.IdealSheafData)
      (_ : I.toSubobject = AlgebraicGeometry.Scheme.denominatorIdealSheaf ℒ s)
      (π : AlgebraicGeometry.Blowup X I),
      AlgebraicGeometry.IsAdmissibleBlowup I.openComplement π.hom)

/- Lemma 31.34.6 (2): on that blowup there is an effective Cartier divisor
`D` and an isomorphism `b^*ℒ ≅ 𝒪(D-E)` carrying the pulled-back meromorphic
section to `1_D ⊗ (1_E)⁻¹`. -/
@[stacks 0ESL] #check
  (AlgebraicGeometry.Blowup.exists_effectiveCartierDivisor_pullbackIso_of_denominatorIdeal :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.IsLocallyNoetherian X]
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (_ : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
      (I : X.IdealSheafData)
      (hI : I.toSubobject = AlgebraicGeometry.Scheme.denominatorIdealSheaf ℒ s)
      (π : AlgebraicGeometry.Blowup X I),
      ∃ (D : π.scheme.IdealSheafData)
        (hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι)
        (σ : @AlgebraicGeometry.Scheme.IdealSheafData.negSheaf
            π.scheme π.exceptionalDivisor
              π.isBlowup.toIsEffectiveCartierDivisor ⟶
          (AlgebraicGeometry.Scheme.Modules.pullback π.hom).obj ℒ)
        (e : (AlgebraicGeometry.Scheme.Modules.pullback π.hom).obj ℒ ≅
          @AlgebraicGeometry.Scheme.IdealSheafData.differenceSheaf
            π.scheme D π.exceptionalDivisor hD
              π.isBlowup.toIsEffectiveCartierDivisor),
        I.idealSheafPullbackComparison π.hom ≫ σ =
            AlgebraicGeometry.Blowup.pullbackDenominatorSectionMap π ℒ s hI ∧
          σ ≫ e.hom =
            @AlgebraicGeometry.Scheme.IdealSheafData.differenceCanonicalSectionHom
              π.scheme D π.exceptionalDivisor hD
                π.isBlowup.toIsEffectiveCartierDivisor)
