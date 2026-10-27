/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.Proper
import StacksCheckRecall

/-!
# Finite-dimensionality of Inf and T for proper schemes over a field

In Lemma 93.9.3, if `X` is proper over `k`, then `Inf(Def_X)` and `T Def_X` are
finite-dimensional `k`-vector spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX] [IsProper hX]

/- Lemma 93.9.4 (1)
In Lemma 93.9.3, if `X` is proper over `k`, then `Inf(Def_X)` is a finite-dimensional
`k`-vector space. -/
@[stacks 0DYA] #check (FlatSchemeCat.instFiniteDimensional_inf Λ k X hX :
  FiniteDimensional k (FlatSchemeCat.inf Λ k X hX))

/- Lemma 93.9.4 (2)
In Lemma 93.9.3, if `X` is proper over `k`, then `T Def_X` is a finite-dimensional
`k`-vector space. -/
@[stacks 0DYA] #check (FlatSchemeCat.instFiniteDimensional_tangentSpace Λ k X hX :
  FiniteDimensional k (FlatSchemeCat.tangentSpace Λ k X hX))
