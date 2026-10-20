/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.Representable
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.7.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is quasi-compact as in Properties
of Stacks, Section 100.3 if and only if for every quasi-compact algebraic
stack `Z` and morphism `Z ⟶ Y` the algebraic stack `Z ×_Y X` is
quasi-compact. -/
@[stacks 050T] #check (AlgebraicGeometry.Groupoids.Hom.has_quasiCompact_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces f),
    AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) f ↔
      AlgebraicStack.QuasiCompact f)
