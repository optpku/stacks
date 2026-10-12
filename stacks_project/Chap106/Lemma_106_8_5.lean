/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_19_2_FormallySmooth
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap106.Definition_106_8_1_FormallySmooth

/-!
# Formally smooth morphisms representable by algebraic spaces

A morphism of algebraic stacks representable by algebraic spaces is formally
smooth if and only if every scheme-slice base change is formally smooth as a
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.8.5. Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is formally smooth if and only if
for every scheme `T` and morphism `T ⟶ Y` the morphism `X ×_Y T ⟶ T` is
formally smooth as a morphism of algebraic spaces. -/
@[stacks 0H1K]
theorem FormallySmooth.iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    FormallySmooth f ↔ Groupoids.Hom.has (@AlgebraicSpace.FormallySmooth S) f :=
  sorry

/-- Formal smoothness of a representable morphism of algebraic stacks is
equivalent to every scheme-slice representing morphism of algebraic spaces
being formally smooth. -/
theorem FormallySmooth.iff_represents {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    FormallySmooth f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → AlgebraicSpace.FormallySmooth fy :=
  sorry

/-- A scheme-slice representing morphism of a formally smooth morphism of
algebraic stacks is formally smooth as a morphism of algebraic spaces. -/
theorem FormallySmooth.spec_represents {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [FormallySmooth f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.FormallySmooth fy :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is formally
smooth if every scheme-slice representing morphism of algebraic spaces is
formally smooth. -/
theorem FormallySmooth.of_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : Groupoids.Hom.has (@AlgebraicSpace.FormallySmooth S) f) :
    FormallySmooth f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
