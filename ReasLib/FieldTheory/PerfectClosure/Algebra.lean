/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PerfectClosure

/-!
# Algebra structure on perfect closures

This file provides the canonical algebra structure induced by the embedding into
the perfect closure of a field.
-/

@[expose] public section

universe u

namespace PerfectClosure

/-- The canonical `k`-algebra structure on the perfect closure of a field of
characteristic `p`. -/
instance instAlgebra {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Algebra k (PerfectClosure k p) :=
  (PerfectClosure.of k p).toAlgebra

end PerfectClosure
