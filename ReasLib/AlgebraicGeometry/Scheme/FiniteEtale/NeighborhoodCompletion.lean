module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Completion from open neighborhoods of the closed support is an equivalence on
finite locally free objects when it is fully faithful on those objects and every
finite locally free coherent formal module is isomorphic, on some open neighborhood,
to the completion of a finite locally free module. -/
def NeighborhoodCompletionIsEquivalence (I : X.IdealSheafData) : Prop :=
  NeighborhoodCompletionFullyFaithful I ∧
    ∀ F : (CoherentFormalModules.finiteLocallyFree X I).FullSubcategory,
      ∃ V : (compactSupport I).openNhds,
        (onFiniteLocallyFree (I.comap (X.ofRestrict V.val.isOpenEmbedding))).essImage
          ((coherentFormalModulesRestrictionFunctor I V.val).obj F.obj)

end AlgebraicGeometry.Scheme.CoherentCompletion

namespace AlgebraicGeometry.Scheme

/-- For a Noetherian scheme, if completion from open neighborhoods of a closed
subscheme is an equivalence on finite locally free objects, then restriction from
the colimit of finite étale neighborhood categories to finite étale schemes over
the closed subscheme is an equivalence. -/
theorem finiteEtaleNeighborhoodRestriction_isEquivalence_of_completion
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (h_completion : CoherentCompletion.NeighborhoodCompletionIsEquivalence I)
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) :
    Functor.IsEquivalence (finiteEtaleNeighborhoodRestriction I t) := sorry

end AlgebraicGeometry.Scheme
