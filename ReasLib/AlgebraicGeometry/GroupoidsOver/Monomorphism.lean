/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Monomorphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is a monomorphism when every representing
morphism of algebraic spaces `Fy ⟶ ofOver U` is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is a
monomorphism when it is representable by algebraic spaces and every
representing morphism `fy : Fy ⟶ ofOver U` is a monomorphism of algebraic
spaces. -/
class Mono {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is a monomorphism. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → CategoryTheory.Mono fy

namespace Mono

/-- The identity 1-morphism of a category fibred in groupoids is a
monomorphism. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Mono (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for a monomorphism of
groupoid fibrations is a monomorphism. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Mono f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    CategoryTheory.Mono fy := Mono.of_represents y Fy fy h

/-- A monomorphism of groupoid fibrations is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Mono f] : relativelyRepresentableByAlgebraicSpaces f := Mono.representable

/-- A 1-morphism is a monomorphism if and only if it is representable by
algebraic spaces and every representing morphism of algebraic spaces is a
monomorphism. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Mono f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → CategoryTheory.Mono fy :=
  ⟨fun h ↦ ⟨h.representable, h.of_represents⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end Mono

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and has the monomorphism property induces a full and faithful
functor on every fibre. -/
theorem has.fiberwiseFullyFaithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {j : X ⟶ Y} (hj : relativelyRepresentableByAlgebraicSpaces j)
    (hmono : has (MorphismProperty.monomorphisms (AlgebraicSpace S)) j)
    (U : Over S) : (fiberFunctor j U).Full ∧ (fiberFunctor j U).Faithful :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
