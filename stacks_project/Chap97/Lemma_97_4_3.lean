module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Diagonals of stacks with an fppf algebraic-space atlas

If a stack in groupoids over `(Sch/S)_fppf` admits a 1-morphism from an
algebraic space that is representable by algebraic spaces, surjective, flat,
and locally of finite presentation, then its diagonal is representable by
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 97.4.3: Let `S` be a scheme. Let `u : U ⟶ X` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `U` is representable by an
algebraic space, and `u` is representable by algebraic spaces, surjective,
flat, and locally of finite presentation, then `Δ : X ⟶ X × X` is
representable by algebraic spaces. -/
@[stacks 05XW]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_of_fppfAtlas
    {S : Scheme.{u}} {X : GroupoidsOver S} {U : AlgebraicSpace S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    (u : U.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective u] [Groupoids.Hom.Flat u]
    [Groupoids.Hom.LocallyOfFinitePresentation u] :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

end AlgebraicGeometry
