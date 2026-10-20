/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper

/-!
# Chow's lemma for algebraic stacks

A separated finite-type morphism from an algebraic stack to a quasi-compact,
absolutely quasi-separated algebraic space admits a proper surjective morphism
from an algebraic space that embeds openly into a proper algebraic space over
the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A separated finite-type morphism from an algebraic stack to a quasi-compact,
absolutely quasi-separated algebraic space admits a proper surjective morphism
`h` from an algebraic space `Z` and an open immersion `j : Z ⟶ Zbar`, where
`Zbar` is proper over the target via `gBar`. The space triangle commutes by
`j ≫ gBar = g`, and the stack triangle commutes up to an invertible 2-cell. -/
theorem exists_isOpenImmersion_proper_surjective
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ Y.toGroupoids)
    [AlgebraicStack.Separated f] [AlgebraicStack.FiniteType f] :
    ∃ (Zbar Z : AlgebraicSpace S) (j : Z ⟶ Zbar) (gBar : Zbar ⟶ Y)
      (g : Z ⟶ Y) (h : Z.toGroupoids ⟶ X),
      AlgebraicSpace.IsOpenImmersion j ∧ AlgebraicSpace.Proper gBar ∧
        AlgebraicStack.Proper h ∧ AlgebraicStack.Surjective h ∧ j ≫ gBar = g ∧
          Nonempty (h ≫ f ≅ AlgebraicSpace.toGroupoids.map g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
