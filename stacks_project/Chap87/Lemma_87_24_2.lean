/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
import StacksCheckRecall

/-!
# Finite type morphisms of formal algebraic spaces versus Bootstrap transfer

A morphism of formal algebraic spaces is of finite type in the sense of
Definition 87.24.1 if and only if it is representable by algebraic spaces and
of finite type in the sense of Bootstrap, Definition 80.4.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.24.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Then `f` is of finite type if and only if
`f` is representable by algebraic spaces and of finite type in the sense of
Bootstrap, Definition 80.4.1. -/
@[stacks 0AJJ] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.IsFiniteType.iff_relativeAlgebraicSpaces :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
      [FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
      [FormalAlgebraicSpace.Reduction X] [FormalAlgebraicSpace.Reduction Y] (f : X ⟶ Y),
      FormalAlgebraicSpace.IsFiniteType f ↔
        AlgebraicSpace.relativeAlgebraicSpaces (@AlgebraicSpace.FiniteType S) f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsFiniteType.iff_finiteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    [FormalAlgebraicSpace.Reduction X] [FormalAlgebraicSpace.Reduction Y] (f : X ⟶ Y),
    FormalAlgebraicSpace.IsFiniteType f ↔ FormalAlgebraicSpace.FiniteType f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsFiniteType.instFiniteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    [FormalAlgebraicSpace.Reduction X] [FormalAlgebraicSpace.Reduction Y]
    (f : X ⟶ Y) [FormalAlgebraicSpace.IsFiniteType f], FormalAlgebraicSpace.FiniteType f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.FiniteType.instIsFiniteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    [FormalAlgebraicSpace.Reduction X] [FormalAlgebraicSpace.Reduction Y]
    (f : X ⟶ Y) [FormalAlgebraicSpace.FiniteType f], FormalAlgebraicSpace.IsFiniteType f)
