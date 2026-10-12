/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Equivalence
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of the canonical normalized quotient

This leaf bundles the canonical normalized image-quotient functor as an exact functor.

@stack 019I
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical normalized image-quotient functor, bundled as an exact functor. -/
@[stacks 019I "bundled exact canonical normalized image quotient"]
noncomputable def exactFunctor :
    CosimplicialObject A ⥤ₑ CochainComplex A ℕ :=
  ExactFunctor.of (functor (A := A))

end CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized
