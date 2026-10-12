/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap97.Lemma_97_7_1_SurjectiveOnObjects
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Surjective on objects versus surjective morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is surjective on objects if and only if it is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace SurjectiveOnObjects

/-- Lemma 97.7.3: Let `p : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `p` is representable by algebraic spaces,
then `p` is surjective on objects if and only if `p` is surjective in the
sense of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 06D7]
theorem iff_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    SurjectiveOnObjects p ↔ Surjective p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is surjective is
surjective on objects. -/
instance of_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [Surjective p] :
    SurjectiveOnObjects p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is surjective on objects if and only if it has the
algebraic-space surjectivity property of Definition 94.10.1. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    SurjectiveOnObjects p ↔ has (@AlgebraicSpace.Surjective S) p :=
  sorry

end SurjectiveOnObjects

namespace Surjective

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and surjective on objects is surjective. -/
theorem of_surjectiveOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
    [SurjectiveOnObjects p] :
    Surjective p :=
  sorry

end Surjective

end AlgebraicGeometry.Groupoids.Hom
