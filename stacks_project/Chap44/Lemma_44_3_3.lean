/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Complement
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/- Lemma 44.3.3: if finite locally free closed subschemes `D₁` and `D₂` of a smooth
relative curve have ranks `d₁` and `d₂`, and `D₁` is contained in `D₂`, then `D₂` is the
sum of `D₁` and a finite locally free closed subscheme of rank `d₂ - d₁`. -/
@[stacks 0B9F] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.exists_complement_of_le :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      (D₁ D₂ : X.IdealSheafData) (d₁ d₂ : ℕ),
      IsFiniteLocallyFreeOfRank (D₁.subschemeι ≫ f) d₁ →
        IsFiniteLocallyFreeOfRank (D₂.subschemeι ≫ f) d₂ →
          D₂ ≤ D₁ →
            ∃ D : X.IdealSheafData,
              IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) (d₂ - d₁) ∧
                D₂ = effectiveCartierDivisorSum D₁ D)

end AlgebraicGeometry.Scheme.IdealSheafData
