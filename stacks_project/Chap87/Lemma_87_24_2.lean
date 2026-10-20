/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap87.Definition_87_24_1
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType

/-!
# Finite type morphisms of formal algebraic spaces versus Bootstrap transfer

A morphism of formal algebraic spaces is of finite type in the sense of
Definition 87.24.1 if and only if it is representable by algebraic spaces and
of finite type in the sense of Bootstrap, Definition 80.4.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace IsFiniteType

/-- Lemma 87.24.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Then `f` is of finite type if and only if
`f` is representable by algebraic spaces and of finite type in the sense of
Bootstrap, Definition 80.4.1. -/
@[stacks 0AJJ]
theorem iff_relativeAlgebraicSpaces {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) :
    IsFiniteType f ↔
      AlgebraicSpace.representableByAlgebraicSpaces f ∧
        ∀ (ha : AlgebraicSpace.representableByAlgebraicSpaces f)
          ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.FiniteType
            (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ) :=
  sorry

/-- A morphism of formal algebraic spaces is of finite type if and only if it
is of finite type in the Bootstrap-transfer sense. -/
theorem iff_finiteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) :
    IsFiniteType f ↔ FiniteType f :=
  sorry

/-- A morphism of finite type in the sense of Definition 87.24.1 is of finite
type in the Bootstrap-transfer sense. -/
instance instFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [IsFiniteType f] :
    FiniteType f :=
  sorry

end IsFiniteType

namespace FiniteType

/-- A Bootstrap-transfer finite-type morphism of formal algebraic spaces is of
finite type in the sense of Definition 87.24.1. -/
instance instIsFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [FiniteType f] :
    IsFiniteType f :=
  sorry

end FiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
