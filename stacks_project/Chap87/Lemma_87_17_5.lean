/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact
import StacksCheckRecall

/-!
# Quasi-compact morphisms of formal algebraic spaces versus Bootstrap transfer

A morphism of formal algebraic spaces representable by algebraic spaces is
quasi-compact in the sense of Definition 87.17.4 if and only if it is
quasi-compact in the sense of Bootstrap, Definition 80.4.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Lemma 87.17.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` which is representable by algebraic spaces.
Then `f` is quasi-compact in the sense of Definition 87.17.4 if and only if
`f` is quasi-compact in the sense of Bootstrap, Definition 80.4.1. -/
@[stacks 0AM2] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.quasiCompact_iff_relativeAlgebraicSpaces :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
      [FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
      (RX : FormalAlgebraicSpace.ReductionData X)
      (RY : FormalAlgebraicSpace.ReductionData Y) (f : X ⟶ Y)
      (hf : AlgebraicSpace.representableByAlgebraicSpaces f),
      FormalAlgebraicSpace.ReductionData.QuasiCompact RX RY f ↔
        AlgebraicSpace.relativeAlgebraicSpaces (S := S) (@AlgebraicSpace.QuasiCompact S) f)
