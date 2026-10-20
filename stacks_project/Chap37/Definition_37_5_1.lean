/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 37.5.1: if `i : Z ⟶ X` is an immersion, then for `n ≥ 1` its `n`th
infinitesimal neighbourhood is the closed subscheme of the canonical open coborder defined by
`i.liftCoborder.ker ^ (n + 1)`. The case `n = 1` is the first-order infinitesimal
neighbourhood. -/
@[stacks 04EY] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.scheme :
    {Z X : AlgebraicGeometry.Scheme.{u}} → (i : Z ⟶ X) →
      [AlgebraicGeometry.IsImmersion i] → ℕ → AlgebraicGeometry.Scheme.{u})
