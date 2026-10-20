/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Coproduct
import StacksCheckRecall

/-!
# Finite coproducts of finite morphisms of algebraic spaces

A finite family of finite morphisms of algebraic spaces with a common target
induces a finite morphism from the coproduct.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

/- Lemma 67.45.11: If `S` is a scheme and `f i : X i ⟶ Y` are finite morphisms of
algebraic spaces over `S` for a finite index type, then the induced fold
`coproductDesc f : coproduct X ⟶ Y` is finite. -/
@[stacks 0CZ2]
#check (AlgebraicGeometry.AlgebraicSpace.isFinite_coproductDesc :
    ∀ {S : Scheme.{u}} {ι : Type v} [Finite ι] [Small.{u} ι]
      {X : ι → AlgebraicSpace S} {Y : AlgebraicSpace S} (f : ∀ i, X i ⟶ Y)
      [∀ i, AlgebraicGeometry.AlgebraicSpace.IsFinite (f i)],
      AlgebraicGeometry.AlgebraicSpace.IsFinite
        (AlgebraicGeometry.AlgebraicSpace.coproductDesc f))
