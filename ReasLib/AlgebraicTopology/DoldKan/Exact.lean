/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Exactness of the normalized Moore complex

The normalized Moore functor is exact because it is an equivalence. This leaf owns the bundled
exact functor; its unbundled exactness statement is the canonical `.property` projection.

@stack 019B
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Abelian.DoldKan.N

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The normalized Moore complex functor, bundled as an exact functor. -/
@[stacks 019B "exact normalized Moore complex functor"]
noncomputable def exactFunctor :
    SimplicialObject A ⥤ₑ ChainComplex A ℕ :=
  ExactFunctor.of N

end CategoryTheory.Abelian.DoldKan.N
