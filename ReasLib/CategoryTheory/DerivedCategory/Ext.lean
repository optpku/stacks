/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

@[expose] public section

/-!
# Extension Groups in the Derived Category

For a derived category `D(𝒜)` of an abelian category `𝒜`, the `i`-th extension group between
two objects `X Y : D(𝒜)` is by definition the group of shifted morphisms `X ⟶ Y⟦i⟧`, equivalently
morphisms `X[-i] ⟶ Y`. This module fixes the source-facing notation `Ext⁽i⁾(X, Y)` for this group,
bridging to Mathlib's canonical owner `ShiftedHom X Y i`.

For objects `A B` of the abelian category `𝒜` itself, Mathlib's `Ext A B n` is the specialization
of the derived extension group to the single complexes `A[0]` and `B[0]`, and `Ext.homEquiv`
identifies `Ext A B n` with `Ext⁽(n : ℤ)⁾(((singleFunctor 𝒜 0).obj A), ((singleFunctor 𝒜 0).obj B))`.

## Main definitions

* `DerivedExt` — scoped notation `Ext⁽n⁾(X, Y)` for `ShiftedHom X Y n`.
-/

namespace CategoryTheory

/-- `Ext⁽n⁾(X, Y)` is notation for the `n`-th shifted morphism group `ShiftedHom X Y n`, the
extension group between `X` and `Y` in the derived category. -/
scoped[DerivedExt] notation:max "Ext⁽" n "⁾(" X ", " Y ")" =>
  CategoryTheory.ShiftedHom X Y n

end CategoryTheory
