/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_21_1_Chart
public import stacks_project.Chap75.Lemma_75_21_1_Pullback
public import stacks_project.Chap75.Lemma_75_21_1_Criteria

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.21.1: for a cartesian square of algebraic spaces over `S`, `K` in
`D_QCoh(𝒪_X)`, and a map `L(g')^* K ⟶ K'` in `D_QCoh(𝒪_{X'})`, invertibility of the
geometric-point maps 75.21.0.1 is equivalent to the criteria of Lemma 36.26.1 on every
étale scheme chart `U, V, V'` with `U' = V' ×_V U`, and on some such chart with
`U' → X'` surjective. -/
@[stacks 0DKG]
theorem cohomologyBaseChange_tfae_etale {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    List.TFAE
      [ cohomologyBaseChangeHolds sq K K' α
      , ∀ c : EtaleBaseChangeChart g' f' f g, c.schemeHolds sq K K' α
      , ∃ c : EtaleBaseChangeChart g' f' f g,
          AlgebraicSpace.Surjective (c.toX' sq) ∧ c.schemeHolds sq K K' α ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
