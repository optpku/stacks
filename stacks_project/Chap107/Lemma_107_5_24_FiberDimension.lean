/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Finite-type points of an algebraic stack

A point of an algebraic stack is of finite type when it is represented by a
morphism `Spec k ⟶ X` that is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsFiniteTypePoint :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
      Points X → Prop)

#check (AlgebraicGeometry.AlgebraicStack.isFiniteTypePoint_iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (x : Points X),
    IsFiniteTypePoint x ↔
      ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x)

#check (AlgebraicGeometry.AlgebraicStack.IsFiniteTypePoint.of_fieldValuedPoint :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) [LocallyOfFiniteType p.hom],
    IsFiniteTypePoint (Points.mk p))

#check (AlgebraicGeometry.AlgebraicStack.IsFiniteTypePoint.exists_fieldValuedPoint :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (hx : IsFiniteTypePoint x),
    ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x)

#check (AlgebraicGeometry.AlgebraicStack.finiteTypePoints :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      Set (Points X))

#check (AlgebraicGeometry.AlgebraicStack.mem_finiteTypePoints_iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X},
    x ∈ finiteTypePoints X ↔ IsFiniteTypePoint x)

end AlgebraicGeometry.AlgebraicStack
