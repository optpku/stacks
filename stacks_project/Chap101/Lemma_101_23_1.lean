/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.Representable
import StacksCheckRecall

/-!
# Representable locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is locally
quasi-finite in the scheme-slice sense of algebraic spaces if and only if it is
locally of finite type and every field-valued 2-fibre has discrete space of
points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.23.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Assume
`f` is representable by algebraic spaces. The following are equivalent: `f` is
locally quasi-finite as in Properties of Stacks, Section 100.3, and `f` is
locally of finite type and for every morphism `Spec(k) ⟶ Y` where `k` is a
field the space `|Spec(k) ×_Y X|` is discrete. -/
@[stacks 06UA] #check (AlgebraicGeometry.Groupoids.Hom.has_locallyQuasiFinite_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y}, relativelyRepresentableByAlgebraicSpaces f →
      (AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f ↔
        AlgebraicStack.LocallyOfFiniteType f ∧ AlgebraicStack.discreteFieldFibers f))
