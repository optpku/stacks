/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- Definition 87.24.1 (1): a morphism `f : Y ⟶ X` of formal algebraic spaces over a
scheme `S` is locally of finite type if it is representable by algebraic spaces
and is locally of finite type in the sense of Bootstrap, Definition 80.4.1, i.e.
the Bootstrap transfer `relativeAlgebraicSpaces (@AlgebraicSpace.LocallyOfFiniteType S)`. -/
@[stacks 0AM4] #check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y), Prop)

/- Definition 87.24.1 (2): a morphism `f : Y ⟶ X` of formal algebraic spaces over a
scheme `S` is of finite type if it is locally of finite type and quasi-compact
in the sense of Definition 87.17.4, i.e. the induced map of algebraic-space
reductions `mapReduction f` is a quasi-compact morphism of algebraic spaces. -/
@[stacks 0AM4] #check (AlgebraicGeometry.FormalAlgebraicSpace.IsFiniteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y), Prop)

/- The identity morphism of a formal algebraic space is of finite type. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.IsFiniteType.id :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X], IsFiniteType (𝟙 X))

/- A morphism of formal algebraic spaces is of finite type when it is locally
of finite type and the induced map of algebraic-space reductions is
quasi-compact. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.IsFiniteType.spec :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [IsFiniteType f],
    LocallyOfFiniteType f ∧ AlgebraicSpace.QuasiCompact (mapReduction f))

end AlgebraicGeometry.FormalAlgebraicSpace
