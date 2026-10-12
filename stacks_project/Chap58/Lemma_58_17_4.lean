/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_15_2_Comparison
public import stacks_project.Chap52.Lemma_52_16_11
public import stacks_project.Chap58.Lemma_58_17_2
public import stacks_project.Chap58.Lemma_58_17_3_Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.NeighborhoodCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 58.17.4: if the neighborhood completion functor
`colim_V Coh(O_V) ⟶ Coh(X, I)`, `F ↦ F^∧`, is an equivalence on finite locally
free objects, then the restriction functor `colim_V FÉt_V ⟶ FÉt_Y` identified
with `finiteEtaleNeighborhoodRestriction I t` is an equivalence. -/
@[stacks 0EK1] #check
  (AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction_isEquivalence_of_completion :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
      (h_completion : AlgebraicGeometry.Scheme.CoherentCompletion.NeighborhoodCompletionIsEquivalence I)
      (t : ColimitCocone (AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodDiagram I)),
      Functor.IsEquivalence (AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction I t))
