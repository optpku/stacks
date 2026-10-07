module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Algebraic stacks from étale stacks with a smooth scheme atlas

An étale stack in groupoids over `(Sch/S)_étale` whose diagonal is representable
by algebraic spaces, and which admits a surjective smooth 1-morphism from a
scheme over `S`, is an algebraic stack in the fppf sense of Definition 94.12.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 97.19.1: denote the common underlying category of `Sch_fppf` and
`Sch_étale` by `Sch_α` (see Sheaves on Stacks, Section 96.4 and Topologies,
Remark 34.11.1), recovered here as the common `Over S` of
`Scheme.etaleTopology` and `Scheme.fppfTopology`. Let `S` be a scheme. Let
`X : GroupoidsOver S` be a category fibred in groupoids over `Sch_α / S`. If
`X` is a stack in groupoids over `(Sch/S)_étale`, i.e.
`[IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]`, the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, and there exists
`U : Over S` with a 1-morphism `u : GroupoidsOver.slice U ⟶ X` which is
surjective and smooth (`[Groupoids.Hom.Smooth u]` and
`[Groupoids.Hom.Surjective u]`), then `X` is an algebraic stack in the sense
of Algebraic Stacks, Definition 94.12.1. -/
@[stacks 076V]
theorem of_etale_smooth_surjective {S : Scheme.{u}} {X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]
    (hΔ : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {U : Over S} (u : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth u] [Groupoids.Hom.Surjective u] :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
