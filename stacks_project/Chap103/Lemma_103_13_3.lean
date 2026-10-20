/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import stacks_project.Chap103.Proposition_103_11_7_Pushforward

/-!
# Lemma 103.13.3

Quasi-coherent pushforward and higher direct images along a quasi-compact
quasi-separated morphism of algebraic stacks preserve coproducts and filtered
colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

namespace qCohHigherDirectImageFunctor

/-- Lemma 103.13.3 (1): Let `f : X ⟶ Y` be a quasi-compact and quasi-separated
morphism of algebraic stacks. Then `qCohHigherDirectImageFunctor f i`
(`f_{QCoh,*}` when `i = 0`, and `R^i f_{QCoh,*}` in general) preserves
coproducts indexed by a type in the ambient universe. -/
@[stacks 0GQX]
instance preservesCoproducts {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (qCohHigherDirectImageFunctor f i) :=
  sorry

/-- Lemma 103.13.3 (2): Let `f : X ⟶ Y` be a quasi-compact and quasi-separated
morphism of algebraic stacks. Then `qCohHigherDirectImageFunctor f i`
(`f_{QCoh,*}` when `i = 0`, and `R^i f_{QCoh,*}` in general) preserves
filtered colimits of shape `J : Type u` with `[Category.{u} J]`. -/
@[stacks 0GQX]
instance preservesFilteredColimits {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} (qCohHigherDirectImageFunctor f i) :=
  sorry

end qCohHigherDirectImageFunctor

end AlgebraicGeometry.GroupoidsOver
