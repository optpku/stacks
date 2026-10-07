module

public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Limit preserving on objects versus locally of finite presentation

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is limit preserving on objects if and only if
it is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreservingOnObjects

/-- Lemma 97.5.3: Let `p : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `p` is representable by algebraic spaces,
then `p` is limit preserving on objects if and only if `p` is locally of finite
presentation in the sense of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 06CX]
theorem iff_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreservingOnObjects p ↔ LocallyOfFinitePresentation p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is locally of finite
presentation is limit preserving on objects. -/
instance of_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [LocallyOfFinitePresentation p] :
    LimitPreservingOnObjects p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving on objects if and only if it has the
algebraic-space locally-of-finite-presentation property of Definition 94.10.1. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreservingOnObjects p ↔
      has (@AlgebraicSpace.LocallyOfFinitePresentation S) p :=
  sorry

end LimitPreservingOnObjects

namespace LocallyOfFinitePresentation

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and limit preserving on objects is locally of finite
presentation. -/
theorem of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
    [LimitPreservingOnObjects p] :
    LocallyOfFinitePresentation p :=
  sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.Groupoids.Hom
