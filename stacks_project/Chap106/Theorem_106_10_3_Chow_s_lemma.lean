/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Chow
import StacksCheckRecall

/-!
# Chow's lemma for algebraic stacks

A separated finite-type morphism from an algebraic stack to a qcqs algebraic
space admits a proper surjective map from an algebraic space that open-immerses
into a proper algebraic space over the same base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Theorem 106.10.3 (Chow's lemma). Let `f : X ⟶ Y` be a morphism from an
algebraic stack to an algebraic space. Assume `Y` is quasi-compact and
quasi-separated, and `f` is separated of finite type. Then there exist
algebraic spaces `Z`, `Zbar` over the same base and morphisms `j : Z ⟶ Zbar`,
`gBar : Zbar ⟶ Y`, `g : Z ⟶ Y`, `h : Z.toGroupoids ⟶ X` forming a
commutative diagram in which `h` is proper surjective, `j` is an open
immersion, and `gBar` is a proper morphism of algebraic spaces.

Here the source stack `𝒳` is `X`, the source space `X` is `Z`, the source
compactification `X̄` is `Zbar`, the source map `X ⟶ 𝒳` is `h`, the source
open immersion `X ⟶ X̄` is `j`, the source proper map `X̄ ⟶ Y` is `gBar`,
and the source down-arrow `X ⟶ Y` is `g`. The space triangle is the equality
`j ≫ gBar = g`, and the stack triangle is a 2-isomorphism
`h ≫ f ≅ AlgebraicSpace.toGroupoids.map g`. -/
@[stacks 0CQ8] #check
  (AlgebraicGeometry.AlgebraicStack.exists_isOpenImmersion_proper_surjective :
    ∀
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ Y.toGroupoids)
    [AlgebraicStack.Separated f] [AlgebraicStack.FiniteType f],
    ∃ (Zbar Z : AlgebraicSpace S) (j : Z ⟶ Zbar) (gBar : Zbar ⟶ Y)
      (g : Z ⟶ Y) (h : Z.toGroupoids ⟶ X),
      AlgebraicSpace.IsOpenImmersion j ∧ AlgebraicSpace.Proper gBar ∧
        AlgebraicStack.Proper h ∧ AlgebraicStack.Surjective h ∧ j ≫ gBar = g ∧
          Nonempty (h ≫ f ≅ AlgebraicSpace.toGroupoids.map g))
