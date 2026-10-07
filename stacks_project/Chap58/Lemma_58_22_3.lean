module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.LocalCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Scheme

universe u

/- Lemma 58.22.3
   In Situation 58.19.1, the restriction functor is fully faithful under the stated
   completeness, regularity, and finite local-cohomology hypotheses. -/
@[stacks 0BLP] #check
  (AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction.fullyFaithful_of_finiteLocalCohomology :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] → [IsLocalRing A] →
      (f : maximalIdeal A) →
      [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A] →
      IsRegular (f : A) →
      [Module.Finite A
        ((localCohomology (maximalIdeal A) 1).obj
          (ModuleCat.of A (A ⧸ Ideal.span ({(f : A)} : Set A))))] →
      let S := AffineAlgebraizationSetup.ofPrincipal (maximalIdeal A) (f : A) f.property
      let I := AffineAlgebraizationSetup.idealOnOpen S
      (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) →
        Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful)
