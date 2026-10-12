/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleNeighborhood
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Every minimal prime away from `f` whose punctured-spectrum point belongs to
the open `U'` has quotient dimension at least two. -/
def minimalPrimeDimGeTwoOn (f : maximalIdeal A) (U' : (scheme A).Opens) : Prop :=
  ∀ p : PrimeSpectrum A,
    p.asIdeal ∈ minimalPrimes A →
      (f : A) ∉ p.asIdeal →
        (hp : p ≠ closedPoint A) →
          point A p hp ∈ U' →
            (2 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)

/-- Restriction of finite étale covers from an open containing the principal
quotient punctured spectrum is faithful when every minimal component of that
open away from `f` has dimension at least two. -/
instance finiteEtaleBaseChange_faithful_of_minimalPrimeDimOn
    [IsNoetherianRing A] (f : maximalIdeal A) (U' : (scheme A).Opens)
    (h0 : Set.range (principalQuotientMap f) ⊆ Set.range U'.ι)
    [hdim : Fact (minimalPrimeDimGeTwoOn f U')] :
    (Scheme.finiteEtaleBaseChange
      (IsOpenImmersion.lift U'.ι (principalQuotientMap f) h0)).Faithful := sorry

/-- The principal quotient punctured spectrum has an open neighborhood in which
every minimal component away from `f` has dimension at least two. -/
theorem exists_open_minimalPrimeDimGeTwoOn [IsNoetherianRing A]
    (f : maximalIdeal A) :
    ∃ U' : (scheme A).Opens,
      Set.range (principalQuotientMap f) ⊆ Set.range U'.ι ∧
        minimalPrimeDimGeTwoOn f U' := sorry

/-- The minimal-prime dimension condition is preserved by shrinking an open
while retaining the image of the principal quotient punctured spectrum. -/
theorem minimalPrimeDimGeTwoOn_mono (f : maximalIdeal A)
    {U' U'' : (scheme A).Opens} (hUU : U'' ≤ U')
    (h0 : Set.range (principalQuotientMap f) ⊆ Set.range U''.ι)
    (hdim : minimalPrimeDimGeTwoOn f U') :
    minimalPrimeDimGeTwoOn f U'' := sorry

/-- Restriction from the colimit of finite étale categories on open neighborhoods
of the principal quotient punctured spectrum to its finite étale category is
faithful for a Noetherian local ring. -/
instance principalNeighborhoodRestriction_faithful [IsNoetherianRing A]
    (f : maximalIdeal A)
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)) :
    (principalNeighborhoodRestriction f t).Faithful := sorry

end AlgebraicGeometry.PuncturedSpectrum
