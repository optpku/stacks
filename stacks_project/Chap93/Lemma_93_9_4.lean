module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap93.Lemma_93_9_3

/-!
# Finite-dimensionality of Inf and T for proper schemes over a field

In Lemma 93.9.3, if `X` is proper over `k`, then `Inf(Def_X)` and `T Def_X` are
finite-dimensional `k`-vector spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX] [IsProper hX]

/-- Lemma 93.9.4 (1)
In Lemma 93.9.3, if `X` is proper over `k`, then `Inf(Def_X)` is a finite-dimensional
`k`-vector space. -/
@[stacks 0DYA, instance]
instance instFiniteDimensional_inf : FiniteDimensional k (inf Λ k X hX) := sorry

/-- Lemma 93.9.4 (2)
In Lemma 93.9.3, if `X` is proper over `k`, then `T Def_X` is a finite-dimensional
`k`-vector space. -/
@[stacks 0DYA, instance]
instance instFiniteDimensional_tangentSpace :
    FiniteDimensional k (tangentSpace Λ k X hX) := sorry

end FlatSchemeCat
