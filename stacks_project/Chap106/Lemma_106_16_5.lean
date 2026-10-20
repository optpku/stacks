/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap106.Lemma_106_16_5_Kunneth

/-!
# Easy Künneth formula for quasi-coherent structure sheaves

If `a : Y ⟶ X` and `b : Z ⟶ X` are representable by schemes, quasi-compact,
quasi-separated, and flat, then the quasi-coherent Künneth morphism of
structure sheaves is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- Lemma 106.16.5. Let `a : Y ⟶ X` and `b : Z ⟶ X` be representable by
schemes, quasi-compact, quasi-separated, and flat. Then
`a_{QCoh,*} O_Y ⊗_{O_X} b_{QCoh,*} O_Z` identifies with
`f_{QCoh,*} O_{Y ×_X Z}` in `QCoh(O_X)`, where `f` is the obvious morphism
from the chosen 2-fibre product. -/
@[stacks 0GRN]
theorem kunnethMap_isIso {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (a : Y ⟶ X) (b : Z ⟶ X)
    (ha : FiberedCategoryOver.Groupoids.relativelyRepresentable a)
    (hb : FiberedCategoryOver.Groupoids.relativelyRepresentable b)
    [AlgebraicStack.QuasiCompact a] [AlgebraicStack.QuasiSeparated a]
    [AlgebraicStack.Flat a]
    [AlgebraicStack.QuasiCompact b] [AlgebraicStack.QuasiSeparated b]
    [AlgebraicStack.Flat b]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)]
    [AlgebraicStack.QuasiCompact (fibreProductHom a b)]
    [AlgebraicStack.QuasiSeparated (fibreProductHom a b)] :
    IsIso (kunnethMap a b) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
