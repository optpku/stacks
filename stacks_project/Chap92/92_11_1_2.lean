/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison
import StacksCheckRecall

/-!
# Truncated comparison from a presentationwise naive cotangent complex

This records the canonical comparison of Stacks 08R9 for arbitrary polynomial arrows.
-/

@[expose] public section

open CategoryTheory
open CommRingCat.Under.FreeAlgebra
open CommRingCat.Under.CotangentComplex
open DerivedCategory.TStructure

universe u

/- 92.11.1.2: let `A ⟶ B` be a ring map. For any object `U = (P ⟶ B)` of `C_{B/A}`,
writing `J = Ker(P ⟶ B)`, there is a canonical morphism
`(J/J² ⟶ Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}` in `D(B)`, obtained by evaluating the
two-term complex `J/J² ⟶ Ω` at `U` and using
`τ_{≥ -1} Lπ_!(J/J² ⟶ Ω) = τ_{≥ -1} L_{B/A}`.
The implemented conormal term is the extension of scalars `(J/J²) ⊗_P B` of the kernel
cotangent module. For an arbitrary nonsurjective arrow, this does not assert an
identification with the raw `P`-module `J/J²`. -/
@[stacks 08R9] #check (Algebra.NaiveCotangent.naiveCotangentToTruncGE :
  ∀ (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B),
    DerivedCategory.Q.obj (naiveComplex A B E φ) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)))
