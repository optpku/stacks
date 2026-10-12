/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy-category characterization of K-projective complexes

This leaf is the projective dual of the K-injective zero-morphism characterization.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

universe v u

namespace CochainComplex.IsKProjective

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A cochain complex is K-projective exactly when every homotopy-category morphism from it to an
acyclic cochain complex is zero. -/
@[stacks 070H "projective dual homotopy-category characterization"]
theorem iff_homotopy_zero (P : CochainComplex A ℤ) :
    P.IsKProjective ↔
      ∀ (M : CochainComplex A ℤ) (hM : M.Acyclic)
        (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient A (up ℤ)).obj M), f = 0 := sorry

end CochainComplex.IsKProjective
