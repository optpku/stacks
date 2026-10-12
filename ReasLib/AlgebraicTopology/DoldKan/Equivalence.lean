/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dold--Kan equivalence instances

Mathlib identifies the normalized Moore complex functor `N` with the forward functor of the
Dold--Kan equivalence by a theorem rather than by definitional equality. This file transports the
canonical equivalence instance across that equality so ordinary typeclass search can use it.

@stack 019G
-/

@[expose] public section

universe v u

namespace CategoryTheory.Abelian.DoldKan.N

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The normalized Moore complex functor is an equivalence of categories. -/
@[stacks 019G]
instance isEquivalence :
    (N : SimplicialObject A ⥤ ChainComplex A ℕ).IsEquivalence :=
  (equivalence_functor (A := A)) ▸ inferInstance

end CategoryTheory.Abelian.DoldKan.N
