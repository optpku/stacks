/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.AddPoint

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Hilbert

/- The shared owner exports the complete add-point API used by chapter consumers. -/
#check
  (AlgebraicGeometry.Hilbert.addPointMap :
    ∀ {S : Scheme.{u}} (X : Over S)
      [SmoothOfRelativeDimension 1 X.hom]
      [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ),
      (functor X d).reprX ⊗ X ⟶ (functor X (d + 1)).reprX)

end AlgebraicGeometry.Hilbert
