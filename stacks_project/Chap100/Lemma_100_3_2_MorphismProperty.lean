/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Representable morphisms of groupoid fibrations having a morphism property

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` has a
property `P` of morphisms of algebraic spaces when every scheme-slice
representing morphism has `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`
has a morphism property `P` of algebraic spaces when every scheme-slice
representing morphism `fy : Fy ⟶ AlgebraicSpace.ofOver U` satisfies `P`. -/
def has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
    (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → P fy

/-- A 1-morphism has `P` if and only if every scheme-slice representing morphism
of algebraic spaces has `P`. -/
theorem has_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    has P f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → P fy :=
  sorry

namespace has

/-- A scheme-slice representing morphism of algebraic spaces for a 1-morphism
that has `P` itself has `P`. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y} (hf : has P f)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    P fy :=
  sorry

/-- A 1-morphism has `P` if every scheme-slice representing morphism of algebraic
spaces has `P`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ AlgebraicSpace.ofOver U),
      RepresentsBaseChange f y Fy fy → P fy) : has P f :=
  sorry

end has

end AlgebraicGeometry.Groupoids.Hom
