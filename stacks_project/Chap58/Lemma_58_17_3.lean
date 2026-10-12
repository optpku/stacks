/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 58.17.3: if the neighborhood completion functor
`colim_V Coh(O_V) ⟶ Coh(X, I)` is fully faithful on finite locally free objects, then the
restriction functor `colim_V FÉt_V ⟶ FÉt_Y` is fully faithful. -/
@[stacks 0ELA] #check
  (AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction_fullyFaithful_of_completion :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
      Scheme.CoherentCompletion.NeighborhoodCompletionFullyFaithful I →
        ∀ (t : ColimitCocone (Scheme.finiteEtaleNeighborhoodDiagram I)),
          Nonempty (Scheme.finiteEtaleNeighborhoodRestriction I t).FullyFaithful)
