module

public import stacks_project.Chap95.Lemma_95_14_10_Comparison
public import stacks_project.Chap95.Lemma_95_14_10_SheafTorsors
public import stacks_project.Chap95.Lemma_95_14_10_Torsors

/-!
# Lemma 95.14.10

The functor sending an fppf algebraic-space `G_U`-torsor to the same object
viewed as an fppf sheaf is an equivalence of stacks in groupoids over
`(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.GroupAlgebraicSpace.Classifying
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Classifying

/-- Lemma 95.14.10: Let `B` be an algebraic space over `S`. Let `G` be a group
algebraic space over `B`. Denote `𝒢`, resp. `ℬ`, the algebraic space `G`,
resp. `B`, seen as a sheaf on `(Sch/S)_fppf`. The functor
`G`-Torsors ⟶ `𝒢/ℬ`-Torsors which associates to a triple `(U, b, X)` the
triple `(U, b, 𝒳)` where `𝒳` is `X` viewed as a sheaf is an equivalence of
stacks in groupoids over `(Sch/S)_fppf`. -/
@[stacks 04UT]
instance toSheafHom_isEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    IsEquivalence (toSheafHom G) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Classifying
