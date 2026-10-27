/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Smooth
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Étale morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is étale when every representing morphism of
algebraic spaces `Fy ⟶ ofOver U` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is étale when
it is representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is an étale morphism of algebraic spaces. -/
class Etale {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is étale. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Etale fy

namespace Etale

/-- For a 1-morphism representable by algebraic spaces, the named étale class
is equivalent to testing étaleness on every representing morphism.

Stacks, Tag 03YK:
`source/stacks-official-a04446e57ec1/additional-sources-1.md:3842-3863`.
The representability hypothesis is needed because `has` only tests existing
representations. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Etale f ↔ has (@AlgebraicSpace.Etale S) f := by
  constructor
  · intro h
    exact h.of_represents
  · intro h
    exact ⟨hf, h⟩

/-- The identity 1-morphism of a category fibred in groupoids is étale. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Etale (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for an étale 1-morphism is
étale. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Etale f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.Etale fy := sorry

/-- An étale 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Etale f] : relativelyRepresentableByAlgebraicSpaces f := sorry

/-- An étale 1-morphism of categories fibred in groupoids is smooth. -/
instance smooth_of_etale {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Etale f] : Smooth f := sorry

end Etale

end AlgebraicGeometry.Groupoids.Hom
