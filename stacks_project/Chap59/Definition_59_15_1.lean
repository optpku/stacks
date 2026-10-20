/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

universe u v

/-
Definition 59.15.1: An fpqc covering of a scheme `T` is an indexed family of
morphisms to `T` whose members are flat and which admits a finite affine
refinement over every affine open of `T`.
-/
@[stacks 03NW] #check (AlgebraicGeometry.Scheme.FpqcCovering :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (ι → CategoryTheory.Over T) → Prop)

#check (AlgebraicGeometry.fpqcCovering_iff_flat_and_hasAffineRefinement :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (family : ι → CategoryTheory.Over T) →
      AlgebraicGeometry.Scheme.FpqcCovering family ↔
        (∀ i : ι, AlgebraicGeometry.Flat (family i).hom) ∧
          AlgebraicGeometry.HasAffineRefinement family)
