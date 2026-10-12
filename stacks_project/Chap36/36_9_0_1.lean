/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.Koszul.PowerTower
import StacksCheckRecall

universe u

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

/- 36.9.0.1: The zero-based stage `n` of this inverse system is
`Iᵇᵘˡˡᵉᵗ (f₁ ^ (n + 1), …, fᵣ ^ (n + 1))`; its successor maps give the displayed
backward arrows. -/
@[stacks 08CY]
#check (KoszulComplex.PowerTower.idealSystem f :
  CategoryTheory.SequentialInverseSystem (CochainComplex (ModuleCat A) ℤ))
