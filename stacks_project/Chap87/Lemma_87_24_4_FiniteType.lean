/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap88.Definition_88_21_1_Formal
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Finite type morphisms of formal algebraic spaces

A morphism of functors of points on schemes over `S` is of finite type when it
is representable by algebraic spaces and every Yoneda pullback is of finite
type as a morphism of algebraic spaces. This is the Bootstrap transfer of
`AlgebraicSpace.FiniteType`, equivalently locally of finite type and
quasi-compact on those pullbacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.FiniteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.FormalAlgebraicSpace.FiniteType.id :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u},
    FormalAlgebraicSpace.FiniteType (𝟙 X))

#check (AlgebraicGeometry.FormalAlgebraicSpace.FiniteType.spec :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : FormalAlgebraicSpace.FiniteType f],
    AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.FiniteType
          (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ))

#check (AlgebraicGeometry.FormalAlgebraicSpace.FiniteType.instLocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [FormalAlgebraicSpace.FiniteType f], FormalAlgebraicSpace.LocallyOfFiniteType f)
