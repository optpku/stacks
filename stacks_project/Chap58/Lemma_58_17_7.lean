/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.NeighborhoodSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.17.7 (1): if `X` is a Noetherian quasi-affine scheme and neighborhood sections of
`𝒪_V` map isomorphically to the inverse limit of sections on the infinitesimal
neighbourhoods of a closed subscheme `Y ⊂ X`, then `colim_V FÉt_V ⟶ FÉt_Y` is fully
faithful. -/
@[stacks 0EK0] #check
  (AlgebraicGeometry.Scheme.FiniteEtaleNeighborhood.fullyFaithful_of_quasiAffine :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (hX : X.IsQuasiAffine)
    (h_complete : Function.Bijective
      (CoherentCompletion.neighborhoodComparison I (SheafOfModules.unit X.ringCatSheaf)))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)),
    Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful)

/- Lemma 58.17.7 (2): if `X` is a Noetherian scheme with an ample invertible module `L`
whose nonnegative tensor powers are eventually neighborhood-complete along the infinitesimal
neighbourhoods of a closed subscheme `Y ⊂ X`, then `colim_V FÉt_V ⟶ FÉt_Y` is fully
faithful. -/
@[stacks 0EK0] #check
  (AlgebraicGeometry.Scheme.FiniteEtaleNeighborhood.fullyFaithful_of_ample :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (L : X.Modules)
    (hL : Modules.isAmpleObject L)
    (h_complete : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Function.Bijective
        (CoherentCompletion.neighborhoodComparison I (RingedSpace.TensorPower.sheaf L m)))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)),
    Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful)

/- Lemma 58.17.7 (3): if `X` is a Noetherian scheme and every finite locally free module on
every open neighborhood `V` of a closed subscheme `Y ⊂ X` is neighborhood-complete along the
infinitesimal neighbourhoods of `Y`, then `colim_V FÉt_V ⟶ FÉt_Y` is fully faithful. -/
@[stacks 0EK0] #check
  (AlgebraicGeometry.Scheme.FiniteEtaleNeighborhood.fullyFaithful_of_finiteLocallyFree :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (h_complete : ∀ (V : (CoherentCompletion.compactSupport I).openNhds)
      (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
      CoherentCompletion.finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
        Function.Bijective (CoherentCompletion.neighborhoodComparison
          (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)),
    Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful)

end AlgebraicGeometry.Scheme
