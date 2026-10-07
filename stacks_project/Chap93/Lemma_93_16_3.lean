module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap93.Lemma_93_16_3_Stalk
public import stacks_project.Chap93.Lemma_93_16_3_Comparison

/-!
# Isolated singularities of scheme deformation categories

If `X` is a separated finite-type scheme over `k` of dimension at most one,
smooth over `k` except at named closed points `p i`, then the maps
`Def_X ⟶ ∏ Def_{O_{X, p i}} ⟶ ∏ Def_{O_{X, p i}^h} ⟶ ∏ Def_{O_{X, p i}^∧}`
exist as morphisms of deformation categories over `C_Λ`. The first arrow is
smooth, and the second and third arrows are smooth and induce isomorphisms on
tangent spaces.
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

/-- A scheme of finite type over the residue field of `C_Λ` is locally Noetherian. -/
theorem isLocallyNoetherian_of_finiteType [Scheme.Hom.FiniteType hX] :
    IsLocallyNoetherian X :=
  sorry

/-- Lemma 93.16.3 (1)
In Example 93.9.1 let `X` be a scheme over `k`. Assume `X` is separated, of
finite type over `k`, and `topologicalKrullDim X ≤ 1`, and that
`X ⟶ Spec(k)` is smooth except at the closed points `p i`. Then the map of
deformation categories `Def_X ⟶ ∏ Def_{O_{X, p i}}` is smooth. -/
@[stacks 0DZP]
theorem isSmooth_stalkPiBasedFunctor [Scheme.Hom.FiniteType hX] [IsSeparated hX]
    (p : ι → X) (hp_closed : ∀ i, p i ∈ closedPoints X) (hp_inj : Function.Injective p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    BasedFunctor.IsSmooth (stalkPiBasedFunctor Λ k X hX p) :=
  sorry

variable [henselianPairInclusion.IsRightAdjoint]

/-- Lemma 93.16.3 (2)
In Example 93.9.1 let `X` be a scheme over `k`. Assume `X` is separated, of
finite type over `k`, and `topologicalKrullDim X ≤ 1`, and that
`X ⟶ Spec(k)` is smooth except at the closed points `p i`. Then the map of
deformation categories `∏ Def_{O_{X, p i}} ⟶ ∏ Def_{O_{X, p i}^h}` is
smooth. -/
@[stacks 0DZP]
theorem isSmooth_henselizationPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X) (hp_inj : Function.Injective p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k X hX p) :=
  sorry

/-- Lemma 93.16.3 (3)
In Example 93.9.1 let `X` be a scheme over `k`. Assume `X` is separated, of
finite type over `k`, and `topologicalKrullDim X ≤ 1`, and that
`X ⟶ Spec(k)` is smooth except at the closed points `p i`. Then the map
`∏ Def_{O_{X, p i}} ⟶ ∏ Def_{O_{X, p i}^h}` induces an isomorphism on
tangent spaces. -/
@[stacks 0DZP]
theorem bijective_differential_henselizationPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X) (hp_inj : Function.Injective p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    Function.Bijective
      (BasedFunctor.differential (henselizationPiBasedFunctor Λ k X hX p)) :=
  sorry

/-- Lemma 93.16.3 (4)
In Example 93.9.1 let `X` be a scheme over `k`. Assume `X` is separated, of
finite type over `k`, and `topologicalKrullDim X ≤ 1`, and that
`X ⟶ Spec(k)` is smooth except at the closed points `p i`. Then the map of
deformation categories `∏ Def_{O_{X, p i}^h} ⟶ ∏ Def_{O_{X, p i}^∧}` is
smooth. -/
@[stacks 0DZP]
theorem isSmooth_completionPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X) (hp_inj : Function.Injective p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k X hX p) :=
  sorry

/-- Lemma 93.16.3 (5)
In Example 93.9.1 let `X` be a scheme over `k`. Assume `X` is separated, of
finite type over `k`, and `topologicalKrullDim X ≤ 1`, and that
`X ⟶ Spec(k)` is smooth except at the closed points `p i`. Then the map
`∏ Def_{O_{X, p i}^h} ⟶ ∏ Def_{O_{X, p i}^∧}` induces an isomorphism on
tangent spaces. -/
@[stacks 0DZP]
theorem bijective_differential_completionPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X) (hp_inj : Function.Injective p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    Function.Bijective
      (BasedFunctor.differential (completionPiBasedFunctor Λ k X hX p)) :=
  sorry

end FlatSchemeCat
