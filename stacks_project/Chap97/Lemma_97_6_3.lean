/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_19_2_FormallySmooth
public import stacks_project.Chap97.«97_6_0_1_Lifting»
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Formal smoothness on objects versus formal smoothness

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is formally smooth on objects if and only if
it is formally smooth in the sense of Algebraic Stacks, Definition 94.10.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace FormallySmoothOnObjects

/-- Lemma 97.6.3: Let `p : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `p` is representable by algebraic spaces,
then `p` is formally smooth on objects if and only if `p` is formally smooth
in the sense of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 06D3]
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y}
    (hp : relativelyRepresentableByAlgebraicSpaces p) :
    FormallySmoothOnObjects p ↔ has (@AlgebraicSpace.FormallySmooth S) p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and has the algebraic-space formally-smooth property of
Definition 94.10.1 is formally smooth on objects. -/
theorem of_has {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y}
    (hp : relativelyRepresentableByAlgebraicSpaces p)
    (h : has (@AlgebraicSpace.FormallySmooth S) p) :
    FormallySmoothOnObjects p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and formally smooth on objects has the algebraic-space
formally-smooth property of Definition 94.10.1. -/
theorem to_has {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y}
    (hp : relativelyRepresentableByAlgebraicSpaces p)
    [FormallySmoothOnObjects p] :
    has (@AlgebraicSpace.FormallySmooth S) p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is formally smooth on objects if and only if every
scheme-slice representing morphism of algebraic spaces is formally smooth. -/
theorem iff_represents {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y}
    (hp : relativelyRepresentableByAlgebraicSpaces p) :
    FormallySmoothOnObjects p ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange p y Fy fy → AlgebraicSpace.FormallySmooth fy :=
  sorry

end FormallySmoothOnObjects

end AlgebraicGeometry.Groupoids.Hom
