/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtaleNeighborhood

/-- For a Noetherian quasi-affine scheme, bijectivity of the structure-module comparison
from neighborhood sections to sections on infinitesimal neighborhoods implies full faithfulness
of restriction from the colimit of finite étale neighborhood categories to the closed subscheme. -/
theorem fullyFaithful_of_quasiAffine
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (hX : X.IsQuasiAffine)
    (h_complete : Function.Bijective
      (CoherentCompletion.neighborhoodComparison I (SheafOfModules.unit X.ringCatSheaf)))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) :
    Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful := sorry

/-- For a Noetherian scheme with an ample invertible module, eventual bijectivity of the
neighborhood-section comparisons for its tensor powers implies full faithfulness of restriction
from the colimit of finite étale neighborhood categories to the closed subscheme. -/
theorem fullyFaithful_of_ample
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (L : X.Modules)
    (hL : Modules.isAmpleObject L)
    (h_complete : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Function.Bijective
        (CoherentCompletion.neighborhoodComparison I (RingedSpace.TensorPower.sheaf L m)))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) :
    Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful := sorry

/-- For a Noetherian scheme, bijectivity of the neighborhood-section comparison for every
finite locally free module on every open neighborhood of a closed subscheme implies full
faithfulness of restriction from the colimit of finite étale neighborhood categories to that
closed subscheme. -/
theorem fullyFaithful_of_finiteLocallyFree
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (h_complete : ∀ (V : (CoherentCompletion.compactSupport I).openNhds)
      (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
      CoherentCompletion.finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
        Function.Bijective (CoherentCompletion.neighborhoodComparison
          (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) :
    Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.FiniteEtaleNeighborhood
