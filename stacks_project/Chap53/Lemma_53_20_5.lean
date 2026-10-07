module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal.SourceLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/- Lemma 53.20.5 (1): for a flat, locally finitely presented morphism, the
at-worst-nodal source locus is the greatest open subscheme on which the restriction is
at-worst-nodal of relative dimension one. -/
@[stacks 0DSC] #check
  (AlgebraicGeometry.AtWorstNodal.sourceLocus_isGreatest :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f],
      IsGreatest
        {U : X.Opens | AlgebraicGeometry.AtWorstNodal (U.ι ≫ f)}
        (MorphismProperty.sourceLocus
          (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) f))

/- Lemma 53.20.5 (2): formation of the maximal at-worst-nodal source locus of a flat,
locally finitely presented morphism commutes with arbitrary base change. -/
@[stacks 0DSC] #check
  (AlgebraicGeometry.AtWorstNodal.sourceLocus_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      (g : S' ⟶ S),
      (pullback.fst f g) ⁻¹ᵁ
          (MorphismProperty.sourceLocus
            (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) f) =
        MorphismProperty.sourceLocus
          (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u})
            (pullback.snd f g))

end AlgebraicGeometry
