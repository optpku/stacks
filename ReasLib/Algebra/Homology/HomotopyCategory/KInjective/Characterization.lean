/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy-category characterization of K-injective complexes

This leaf exposes the homotopy-category zero-morphism form of Mathlib's canonical
`CochainComplex.IsKInjective` class without introducing a local name for the quotient functor.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

universe v u

namespace CochainComplex.IsKInjective

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A cochain complex is K-injective exactly when every homotopy-category morphism to it from an
acyclic cochain complex is zero. -/
@[stacks 070H "K-injective homotopy-category characterization"]
theorem iff_homotopy_zero (I : CochainComplex A ℤ) :
    I.IsKInjective ↔
      ∀ (M : CochainComplex A ℤ) (hM : M.Acyclic)
        (f : (HomotopyCategory.quotient A (up ℤ)).obj M ⟶
          (HomotopyCategory.quotient A (up ℤ)).obj I), f = 0 := sorry

end CochainComplex.IsKInjective
