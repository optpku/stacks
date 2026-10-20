/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import StacksCheckRecall

/-!
@stack 019G

# Source-facing recall for Theorem 14.24.3

Mathlib's abelian Dold-Kan equivalence uses the normalized Moore complex as its forward functor.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Abelian.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Theorem 14.24.3: the normalized Moore complex functor induces the Dold-Kan equivalence. -/
@[stacks 019G]
#check (equivalence : SimplicialObject A ≌ ChainComplex A ℕ)

#check (N : SimplicialObject A ⥤ ChainComplex A ℕ)
@[stacks 019G "Theorem 14.24.3, normalized Moore forward functor"]
#check (equivalence_functor (A := A) :
  (equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor = N)
#check (equivalence_inverse (A := A))

end CategoryTheory.Abelian.DoldKan
