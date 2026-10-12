/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteLocalRing

/-!
# Failure of base-field compatibility for completed local rings

A completed local ring of a locally Noetherian scheme over a field need not
have a power-series presentation compatible with the base-field algebra
structure.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- There exist a field, a locally Noetherian scheme over that field, and a
point such that no quotient of a finite-variable formal power series ring over
the residue field is algebra-equivalent over the base field to the completed
local ring at the point. -/
@[stacks 0C52]
theorem exists_no_powerSeriesQuotientAlgEquiv_completedStalk :
    ∃ (k : Type u) (_ : Field k)
      (X : Over (Spec (CommRingCat.of k))) (_ : IsLocallyNoetherian X.left)
      (x : X.left),
      ¬ ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.left.residueField x))),
        Nonempty
          ((MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I) ≃ₐ[k]
            AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
              (X.left.presheaf.stalk x)) := sorry

end AlgebraicGeometry.SchemeOverField
