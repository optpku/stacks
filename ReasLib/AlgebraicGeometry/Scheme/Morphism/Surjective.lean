/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Surjective morphisms and affine opens

This file records the scheme-theoretic consequence of a surjective image being contained in an
affine open of its target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Surjective

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- An open subset containing the range of a surjective morphism is the whole target. -/
@[stacks 01KX "open containing a surjective image"]
theorem open_eq_top_of_range_subset [Surjective f] {V : Y.Opens}
    (h_range : Set.range f.base ⊆ (V : Set Y)) :
    V = ⊤ := sorry

/-- If the range of a surjective morphism is contained in an affine open, then its target is
affine. -/
@[stacks 01KX "surjective image contained in an affine open"]
theorem isAffine_of_range_subset_affineOpen [Surjective f]
    {V : Y.Opens} (hV : IsAffineOpen V)
    (h_range : Set.range f.base ⊆ (V : Set Y)) :
    IsAffine Y := sorry

/-- The range of a surjection onto a nonaffine scheme is not contained in any affine open. -/
@[stacks 01KX "surjective image in a nonaffine target"]
theorem not_range_subset_affineOpen [Surjective f] (hY : ¬ IsAffine Y) :
    ¬ ∃ V : Y.Opens, IsAffineOpen V ∧ Set.range f.base ⊆ (V : Set Y) := sorry

end AlgebraicGeometry.Surjective
