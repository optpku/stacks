/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bicategorical equivalences induced by equality

This leaf packages equality transport between bicategory objects as the canonical
adjoint equivalence and exposes its stable morphism-level computations.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Bicategory

/-- An equality of bicategory objects determines the canonical adjoint equivalence carried by
`eqToHom` in both directions. -/
@[stacks 0040 "equivalence induced by object equality"]
def eqToEquivalence {x y : B} (h : x = y) : x ≌ y :=
  h ▸ Equivalence.id x

/-- Reflexive equality induces the identity bicategorical equivalence. -/
@[simp]
theorem eqToEquivalence.refl (x : B) :
    eqToEquivalence (rfl : x = x) = Equivalence.id x := sorry

/-- The forward morphism of `eqToEquivalence h` is `eqToHom h`. -/
@[simp]
theorem eqToEquivalence.hom {x y : B} (h : x = y) :
    (eqToEquivalence h).hom = eqToHom h := sorry

/-- The inverse morphism of `eqToEquivalence h` is `eqToHom h.symm`. -/
@[simp]
theorem eqToEquivalence.inv {x y : B} (h : x = y) :
    (eqToEquivalence h).inv = eqToHom h.symm := sorry

end Bicategory

end CategoryTheory
