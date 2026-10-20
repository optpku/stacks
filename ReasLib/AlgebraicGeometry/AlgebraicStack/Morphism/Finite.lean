/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Integral and finite morphisms of algebraic stacks

A morphism of algebraic stacks is integral, respectively finite, when it is
representable by algebraic spaces and has the algebraic-space integral,
respectively finite, property on scheme-slice tests.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is integral when it is representable by
algebraic spaces and has the algebraic-space integral property on scheme-slice
representing morphisms. -/
@[mk_iff]
class IsIntegralHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every scheme-slice representing morphism of algebraic spaces is integral. -/
  has_isIntegralHom : Groupoids.Hom.has (@AlgebraicSpace.IsIntegralHom S) f

/-- A morphism of algebraic stacks is finite when it is representable by
algebraic spaces and has the algebraic-space finite property on scheme-slice
representing morphisms. -/
@[mk_iff]
class IsFinite {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every scheme-slice representing morphism of algebraic spaces is finite. -/
  has_isFinite : Groupoids.Hom.has (@AlgebraicSpace.IsFinite S) f

namespace IsIntegralHom

/-- The identity morphism of an algebraic stack is integral. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsIntegralHom (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is integral. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    IsIntegralHom f :=
  sorry

/-- A representing morphism of algebraic spaces for an integral morphism of
algebraic stacks is integral. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIntegralHom f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsIntegralHom fy :=
  sorry

/-- An integral morphism of algebraic stacks is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIntegralHom f] :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- An integral morphism of algebraic stacks is representable by schemes. -/
theorem relativelyRepresentable_scheme {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIntegralHom f] :
    FiberedCategoryOver.Groupoids.relativelyRepresentable f :=
  sorry

/-- An integral morphism of algebraic spaces induces an integral morphism of
the associated algebraic stacks. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.IsIntegralHom f] :
    IsIntegralHom (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end IsIntegralHom

namespace IsFinite

/-- The identity morphism of an algebraic stack is finite. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsFinite (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is finite. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    IsFinite f :=
  sorry

/-- A representing morphism of algebraic spaces for a finite morphism of
algebraic stacks is finite. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsFinite f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsFinite fy :=
  sorry

/-- A finite morphism of algebraic stacks is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsFinite f] :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A finite morphism of algebraic stacks is representable by schemes. -/
theorem relativelyRepresentable_scheme {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsFinite f] :
    FiberedCategoryOver.Groupoids.relativelyRepresentable f :=
  sorry

/-- A finite morphism of algebraic spaces induces a finite morphism of the
associated algebraic stacks. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.IsFinite f] :
    IsFinite (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end IsFinite

/-- A finite morphism of algebraic stacks is integral. -/
instance (priority := 900) instIsIntegralHom_of_isFinite
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsFinite f] :
    IsIntegralHom f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
