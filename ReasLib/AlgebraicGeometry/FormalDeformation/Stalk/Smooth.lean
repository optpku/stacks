/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential
public import ReasLib.AlgebraicGeometry.FormalDeformation.Stalk.Comparison

/-!
# Smoothness of local comparisons of scheme deformations

For a separated finite-type curve over a field, comparison with deformations
of the stalks at distinct closed points containing the nonsmooth locus is smooth.
The subsequent product henselization and completion comparisons are smooth and
induce bijections on tangent spaces.
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

/-- The deformation functor of a separated finite-type scheme over a field of
dimension at most one maps smoothly to the product of its stalk deformation
categories at a finite family of distinct closed points containing its nonsmooth locus. -/
theorem isSmooth_stalkPiBasedFunctor [Scheme.Hom.FiniteType hX] [IsSeparated hX]
    (p : ι → X) (hp_closed : ∀ i, p i ∈ closedPoints X) (hp_inj : Function.Injective p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    BasedFunctor.IsSmooth (stalkPiBasedFunctor Λ k X hX p) :=
  sorry

/-- The stalk comparison is smooth when a finite injective family of closed
points contains the nonsmooth locus of a separated finite-type curve. -/
instance instIsSmooth_stalkPiBasedFunctor [Scheme.Hom.FiniteType hX] [IsSeparated hX]
    (p : ι → X) [Fact (∀ i, p i ∈ closedPoints X)] [Fact (Function.Injective p)]
    [Fact (topologicalKrullDim X ≤ 1)]
    [Fact ({x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p)] :
    BasedFunctor.IsSmooth (stalkPiBasedFunctor Λ k X hX p) :=
  isSmooth_stalkPiBasedFunctor Λ k X hX p Fact.out Fact.out Fact.out Fact.out

variable [henselianPairInclusion.IsRightAdjoint]

/-- For a separated finite-type scheme over a field of dimension at most one,
smooth away from a finite family of closed points, the product comparison from
stalk deformations to henselized stalk deformations is smooth. -/
theorem isSmooth_henselizationPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k X hX p) :=
  sorry

/-- For a separated finite-type scheme over a field of dimension at most one,
smooth away from a finite family of closed points, the product henselization
comparison induces a bijection on tangent spaces. -/
theorem bijective_differential_henselizationPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    Function.Bijective
      (BasedFunctor.differential (henselizationPiBasedFunctor Λ k X hX p)) :=
  sorry

/-- For a separated finite-type scheme over a field of dimension at most one,
smooth away from a finite family of closed points, the product comparison from
henselized stalk deformations to completed stalk deformations is smooth. -/
theorem isSmooth_completionPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k X hX p) :=
  sorry

/-- For a separated finite-type scheme over a field of dimension at most one,
smooth away from a finite family of closed points, the product comparison from
henselized stalk deformations to completed stalk deformations induces a bijection
on tangent spaces. -/
theorem bijective_differential_completionPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    (hp_closed : ∀ i, p i ∈ closedPoints X)
    (hdim : topologicalKrullDim X ≤ 1)
    (hsmooth : {x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p) :
    Function.Bijective
      (BasedFunctor.differential (completionPiBasedFunctor Λ k X hX p)) :=
  sorry

/-- The product henselization comparison is smooth for a separated finite-type
curve smooth away from a finite family of closed points. -/
instance instIsSmooth_henselizationPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    [Fact (∀ i, p i ∈ closedPoints X)] [Fact (topologicalKrullDim X ≤ 1)]
    [Fact ({x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p)] :
    BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k X hX p) :=
  isSmooth_henselizationPiBasedFunctor Λ k X hX p Fact.out Fact.out Fact.out

/-- The product henselization-to-completion comparison is smooth for a separated
finite-type curve smooth away from a finite family of closed points. -/
instance instIsSmooth_completionPiBasedFunctor [Scheme.Hom.FiniteType hX]
    [IsSeparated hX] [IsLocallyNoetherian X] (p : ι → X)
    [Fact (∀ i, p i ∈ closedPoints X)] [Fact (topologicalKrullDim X ≤ 1)]
    [Fact ({x : X | ¬ Scheme.Hom.SmoothAt hX x} ⊆ Set.range p)] :
    BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k X hX p) :=
  isSmooth_completionPiBasedFunctor Λ k X hX p Fact.out Fact.out Fact.out

end FlatSchemeCat
