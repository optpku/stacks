/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Difference
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator.Locus

/-!
# Blowups of denominator ideals

Blowing up the denominator ideal of a regular meromorphic section is
admissible over its regularity locus and resolves the section as a difference
of effective Cartier divisors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Blowup

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- Pulling back multiplication by a meromorphic section on its denominator
ideal gives a morphism from the pulled-back center ideal to the pulled-back
invertible module. -/
noncomputable def pullbackDenominatorSectionMap
    (π : Blowup X I) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hI : I.toSubobject = Scheme.denominatorIdealSheaf ℒ s) :
    (Scheme.Modules.pullback π.hom).obj
        (Subobject.underlying.obj I.toSubobject) ⟶
      (Scheme.Modules.pullback π.hom).obj ℒ :=
  (Scheme.Modules.pullback π.hom).map
    (eqToHom (congrArg Subobject.underlying.obj hI) ≫
      Scheme.denominatorSectionMap ℒ s)

/-- The blowup of the denominator ideal of a regular meromorphic section is
admissible over the open locus where the section is regular. -/
theorem isAdmissible_denominatorIdeal
    [IsLocallyNoetherian X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (I : X.IdealSheafData)
    (hI : I.toSubobject = Scheme.denominatorIdealSheaf ℒ s)
    (π : Blowup X I) :
    IsAdmissibleBlowup I.openComplement π.hom := sorry

/-- On the blowup of a denominator ideal, the pulled-back meromorphic section
is represented by the canonical section of a difference of effective Cartier
divisors. -/
theorem exists_effectiveCartierDivisor_pullbackIso_of_denominatorIdeal
    [IsLocallyNoetherian X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (I : X.IdealSheafData)
    (hI : I.toSubobject = Scheme.denominatorIdealSheaf ℒ s)
    (π : Blowup X I) :
    ∃ (D : π.scheme.IdealSheafData)
      (hD : IsEffectiveCartierDivisor D.subschemeι)
      (σ : @Scheme.IdealSheafData.negSheaf π.scheme π.exceptionalDivisor
          π.isBlowup.toIsEffectiveCartierDivisor ⟶
        (Scheme.Modules.pullback π.hom).obj ℒ)
      (e : (Scheme.Modules.pullback π.hom).obj ℒ ≅
        @Scheme.IdealSheafData.differenceSheaf π.scheme D π.exceptionalDivisor
          hD π.isBlowup.toIsEffectiveCartierDivisor),
      I.idealSheafPullbackComparison π.hom ≫ σ =
          pullbackDenominatorSectionMap π ℒ s hI ∧
        σ ≫ e.hom =
          @Scheme.IdealSheafData.differenceCanonicalSectionHom
            π.scheme D π.exceptionalDivisor hD
              π.isBlowup.toIsEffectiveCartierDivisor := sorry

end AlgebraicGeometry.Blowup
