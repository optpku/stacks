module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Stalk.Smooth
import StacksCheckRecall

/-!
# Isolated singularities of scheme deformation categories
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor RingPairCat
open scoped BasedFunctor

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]
variable {ι : Type u} [Finite ι]

/- Lemma 93.16.3
For a separated finite-type scheme over a field of dimension at most one,
smooth away from the distinct closed points in a finite family, the canonical
stalk comparison is smooth. The following product henselization and completion
comparisons are smooth and induce isomorphisms on tangent spaces. -/
@[stacks 0DZP] #check (FlatSchemeCat.isSmooth_stalkPiBasedFunctor Λ k X hX :
  ∀ [Scheme.Hom.FiniteType hX] [IsSeparated hX]
    (p : ι → X) (hp_closed : ∀ i, p i ∈ closedPoints X) (hp_inj : Function.Injective p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p),
    BasedFunctor.IsSmooth (stalkPiBasedFunctor Λ k X hX p))

variable [henselianPairInclusion.IsRightAdjoint]

#check (FlatSchemeCat.isSmooth_henselizationPiBasedFunctor Λ k X hX :
  ∀ [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p),
    BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k X hX p))

#check (FlatSchemeCat.bijective_differential_henselizationPiBasedFunctor Λ k X hX :
  ∀ [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p),
    Function.Bijective
      (BasedFunctor.differential (henselizationPiBasedFunctor Λ k X hX p)))

#check (FlatSchemeCat.isSmooth_completionPiBasedFunctor Λ k X hX :
  ∀ [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p),
    BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k X hX p))

#check (FlatSchemeCat.bijective_differential_completionPiBasedFunctor Λ k X hX :
  ∀ [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p),
    Function.Bijective
      (BasedFunctor.differential (completionPiBasedFunctor Λ k X hX p)))

end FlatSchemeCat
