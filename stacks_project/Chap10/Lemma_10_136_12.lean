module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Local
import StacksCheckRecall

@[expose] public section

/-!
# Local Consequences of a Relative Global Complete Intersection Presentation

The reusable presentation-level results live in
`ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Local`. This file
keeps the explicit polynomial-quotient formulations of Lemma 10.136.12 as
source-facing bridges where the chapter API is still consumed downstream.
The former chapter-local flatness and cotangent wrappers are intentionally
recalled from that owner instead of being re-exported under chapter names.

@stack 00SV
-/

noncomputable section

universe u

namespace Algebra

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ}
variable (f : Fin c → MvPolynomial (Fin n) R)

-- Local declaration justification (source-local notation): these aliases spell the source's
-- explicit polynomial quotient; reusable localization and cotangent operations remain owned by
-- `Algebra.Presentation` in ReasLib.
local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal
local notation "PresentedPresentation" =>
  (Algebra.Presentation.naive : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c))
local notation "PolynomialRing" => MvPolynomial (Fin n) R

/-- Lemma 10.136.12 (1), tag `00SV`: if
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete intersection,
then at every prime of `S` the displayed relations form a regular sequence in
the corresponding local polynomial ring. -/
@[stacks 00SV "(1) localized relations of a relative global complete intersection are regular"]
theorem relativeGCI_localized_relations_isRegular
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    RingTheory.Sequence.IsRegular A ((List.ofFn f).map (algebraMap PolynomialRing A)) := sorry

end

end Algebra

/- Lemma 10.136.12 (1): the reusable owner-level regular-sequence statement. -/
@[stacks 00SV "(1) localized relations of a relative global complete intersection are regular"]
#check @Algebra.Presentation.IsRelativeGlobalCompleteIntersection.relations_isRegular_atPrime

/- Lemma 10.136.12 (2), tag `00SV`: the reusable owner-level statement for
flat quotients by initial relation segments. -/
@[stacks 00SV "(2) localized relation prefix quotients are flat"]
#check @Algebra.Presentation.IsRelativeGlobalCompleteIntersection.relationPrefixQuotient_flat_atPrime

/- Lemma 10.136.12 (3), tag `00SV`: the reusable owner-level statement for
the cotangent basis of the naive presentation. -/
@[stacks 00SV "(3) naive quotient cotangent basis"]
#check @Algebra.Presentation.IsRelativeGlobalCompleteIntersection.exists_basisCotangent_naive
