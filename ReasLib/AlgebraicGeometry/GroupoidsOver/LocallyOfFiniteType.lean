/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Locally of finite type morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is locally of finite type when every
representing morphism of algebraic spaces `Fy ⟶ ofOver U` is locally of finite
type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is locally of
finite type when it is representable by algebraic spaces and every representing
morphism `fy : Fy ⟶ ofOver U` is a locally of finite type morphism of algebraic
spaces. -/
class LocallyOfFiniteType {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is locally of finite type. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.LocallyOfFiniteType fy

namespace LocallyOfFiniteType

/-- For a 1-morphism representable by algebraic spaces, the named local finite
type class is equivalent to testing local finite type on every representing
morphism.

Stacks, Tag 03YK:
`source/stacks-official-a04446e57ec1/additional-sources-1.md:3842-3863`.
The representability hypothesis is needed because `has` only tests existing
representations. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    LocallyOfFiniteType f ↔ has (@AlgebraicSpace.LocallyOfFiniteType S) f := by
  constructor
  · intro h
    exact h.of_represents
  · intro h
    exact ⟨hf, h⟩

/-- The identity 1-morphism of a category fibred in groupoids is locally of
finite type. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : LocallyOfFiniteType (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for a locally of finite type
1-morphism is locally of finite type. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.LocallyOfFiniteType fy :=
  sorry

/-- A locally of finite type 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A 1-morphism is locally of finite type if and only if it is representable by
algebraic spaces and every representing morphism of algebraic spaces is locally
of finite type. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → AlgebraicSpace.LocallyOfFiniteType fy :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.Groupoids.Hom
