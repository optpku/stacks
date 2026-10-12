/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/-!
# Lemma 33.36.8 compatibility entry point

The reusable finite-relative-Frobenius instance is owned by
`ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties`.
-/

/- Lemma 33.36.8: if `f : X ⟶ S` is locally of finite type and `S` has prime
characteristic `p`, then the relative Frobenius of `f` is finite. -/
@[stacks 0CCD] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isFinite :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] [LocallyOfFiniteType f],
      IsFinite (Scheme.Hom.relativeFrobenius f))
