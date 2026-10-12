/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
# Algebraic stacks from a representable diagonal and Artin's axioms

If `S` is locally Noetherian, `X` is a category fibred in groupoids over
`(Sch/S)_fppf` whose diagonal is representable by algebraic spaces, and `X`
satisfies axioms [-1], [0], [1], [2], [3], effectiveness of formal objects,
openness of versality, and G-rings at finite-type points, then `X` is an
algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 98.17.1: let `S` be a locally Noetherian scheme and let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume (1) the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, (2) `X` satisfies axioms
[-1], [0], [1], [2], [3], (3) every formal object of `X` is effective, (4) `X`
satisfies openness of versality, and (5) `𝒪_{S,s}` is a G-ring for every finite
type point `s` of `S`. Then `X` is an algebraic stack. -/
@[stacks 07Y4]
theorem of_representableDiagonal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]
    [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X] [OpennessOfVersality X]
    [HasBoundedFiniteTypeFibers X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObject X, FormalObject.IsEffective ξ)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
