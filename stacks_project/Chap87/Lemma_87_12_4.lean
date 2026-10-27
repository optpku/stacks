/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Surjective
import StacksCheckRecall

/-!
# Surjectivity of representable morphisms of formal algebraic spaces

A morphism of formal algebraic spaces representable by algebraic spaces is
surjective in the Bootstrap 80.4.1 sense if and only if the induced map of
reductions is a surjective morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.12.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` which is representable by algebraic spaces.
Then `f` is surjective in the sense of Bootstrap, Definition 80.4.1 if and
only if the canonical induced morphism `RX.map RY f` between the reductions
`RX` and `RY` is a surjective morphism of algebraic spaces. -/
@[stacks 0GB8]
#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.surjective_pullback_iff :
  ∀ {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    (RX : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X)
    (RY : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData Y) {f : X ⟶ Y}
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f),
    (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hf.pullbackHom ξ)) ↔
      AlgebraicSpace.Surjective (RX.map RY f))
