/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Colimit preservation by quasi-coherent higher direct images -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

namespace qCohHigherDirectImageFunctor

/-- Quasi-coherent higher direct image along a quasi-compact quasi-separated
morphism of algebraic stacks preserves coproducts indexed by a type in the
ambient universe. -/
instance preservesCoproducts {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (qCohHigherDirectImageFunctor f i) := sorry

/-- Quasi-coherent higher direct image along a quasi-compact quasi-separated
morphism of algebraic stacks preserves filtered colimits of shape `J : Type u`
with `[Category.{u} J]`. -/
instance preservesFilteredColimits {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} (qCohHigherDirectImageFunctor f i) := sorry

end qCohHigherDirectImageFunctor

end AlgebraicGeometry.GroupoidsOver
