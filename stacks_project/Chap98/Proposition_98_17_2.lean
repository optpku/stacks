module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap98.Definition_98_9_4_Effective
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Lemma_98_13_8_Predeformations
public import stacks_project.Chap98.Lemma_98_17_1_BoundedFibers
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic stacks from a representable second diagonal and Artin's axioms

If `S` is locally Noetherian, `X` is a category fibred in groupoids over
`(Sch/S)_fppf` whose second diagonal is representable by algebraic spaces, and
`X` satisfies axioms [-1]–[5] together with G-rings at finite-type points, then
`X` is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids (Hom.diagonal)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Proposition 98.17.2: let `S` be a locally Noetherian scheme and let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the second diagonal
`Δ_Δ = Hom.diagonal (diagonal X) : X ⟶ X ×_{X × X} X` is representable by
algebraic spaces, `X` satisfies axioms [-1], [0], [1], [2], [3], [4], and [5]
of Section 98.14 (`HasBoundedFiniteTypeFibers`, étale `IsStack.InGroupoids`,
`LimitPreserving`, `HasRimSchlessinger`, `HasFiniteDimensionalPredeformations`,
`(approximation X).IsEquivalence`, and `OpennessOfVersality` of both `X` and
`Δ : X ⟶ X × X`), and `𝒪_{S,s}` is a G-ring for every finite type point `s` of
`S`. Then `X` is an algebraic stack. -/
@[stacks 07Y5]
theorem of_representableSecondDiagonal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]
    [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X]
    [(approximation X).IsEquivalence]
    [GroupoidsOver.OpennessOfVersality X]
    [Groupoids.Hom.OpennessOfVersality
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)]
    [HasBoundedFiniteTypeFibers X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
