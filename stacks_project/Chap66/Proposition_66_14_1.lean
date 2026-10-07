module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.FiniteLocallyFree

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

open AlgebraicGeometry

/- Proposition 66.14.1 -/
@[stacks 07S6] #check
  (AlgebraicGeometry.GroupoidScheme.exists_finiteLocallyFree_fppfQuotient :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      [IsFiniteLocallyFree G.s.left] → [IsFiniteLocallyFree G.t.left] →
        [IsEquivalenceRelation G.t G.s] →
          [GroupoidScheme.HasAffineOrbitClosedPoint G] →
            ∃ (M : Over S) (q : G.U ⟶ M)
              (h : G.toPreRelation.t ≫ q = G.toPreRelation.s ≫ q),
              IsFiniteLocallyFree q.left ∧
                IsIso (G.toPreRelation.kernelPairLift q h) ∧
                  IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
                    (StandardTopology.fppf.overTopology S)
                    (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
                    q h))
