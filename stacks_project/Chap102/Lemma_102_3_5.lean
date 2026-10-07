module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap102.Definition_102_3_1_LimitPreserving

/-!
# Limit-preserving 1-morphisms versus locally of finite presentation

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is limit preserving if and only if it is
limit preserving on objects, if and only if it is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreserving

/-- Lemma 102.3.5: Let `p : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `p` is representable by algebraic spaces,
then the following are equivalent: `p` is limit preserving, `p` is limit
preserving on objects, and `p` is locally of finite presentation in the sense
of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 0CMV]
theorem tfae {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    (hp : relativelyRepresentableByAlgebraicSpaces p) :
    List.TFAE [LimitPreserving p, LimitPreservingOnObjects p,
      LocallyOfFinitePresentation p] := sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving if and only if it is limit preserving on
objects. -/
theorem iff_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreserving p ↔ LimitPreservingOnObjects p := sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving if and only if it is locally of finite
presentation. -/
theorem iff_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreserving p ↔ LocallyOfFinitePresentation p := sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and limit preserving on objects is limit preserving. -/
theorem of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
    [LimitPreservingOnObjects p] :
    LimitPreserving p := sorry

/-- A 1-morphism of categories fibred in groupoids that is locally of finite
presentation is limit preserving. -/
instance of_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [LocallyOfFinitePresentation p] :
    LimitPreserving p := sorry

end LimitPreserving

end AlgebraicGeometry.Groupoids.Hom
