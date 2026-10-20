/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ComplementaryDiagonal
import StacksCheckRecall

universe u

/- Example 42.68.21: for a field `k` and unit families `u : Fin a → kˣ` and
`v : Fin b → kˣ`, the determinant of the exact two-periodic complex with
complementary diagonal differentials is the residue-field image of
`(∏ i, u i) / (∏ j, v j)`. -/
@[stacks 02PR] #check
  (CategoryTheory.TwoPeriodicEndomorphism.ComplementaryDiagonal.determinant_eq :
    ∀ {k : Type u} [Field k] {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ),
      CategoryTheory.TwoPeriodicEndomorphism.determinant
          (CategoryTheory.TwoPeriodicEndomorphism.ComplementaryDiagonal.complex u v)
          (CategoryTheory.TwoPeriodicEndomorphism.ComplementaryDiagonal.complex_isFiniteLength u v)
          (CategoryTheory.TwoPeriodicEndomorphism.ComplementaryDiagonal.complex_acyclic u v) =
        Units.map (IsLocalRing.residue k).toMonoidHom
          ((∏ i, u i) / (∏ j, v j)))
