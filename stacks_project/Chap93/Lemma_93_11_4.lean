/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap93.Lemma_93_11_3

/-!
# Finite-dimensionality of Inf and T for proper algebraic spaces over a field

In Lemma 93.11.3, if `X` is proper over `k`, then `Inf(Def_X)` and `T Def_X` are
finite-dimensional `k`-vector spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open FlatAlgebraicSpaceCat

universe u

namespace FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))
variable [AlgebraicSpace.Proper (toBase X)]

/-- Lemma 93.11.4 (1)
In Lemma 93.11.3, if `X` is proper over `k`, then `Inf(Def_X)` is a finite-dimensional
`k`-vector space. -/
@[stacks 0E42, instance]
instance instFiniteDimensional_inf : FiniteDimensional k (inf Λ k X) := sorry

/-- Lemma 93.11.4 (2)
In Lemma 93.11.3, if `X` is proper over `k`, then `T Def_X` is a finite-dimensional
`k`-vector space. -/
@[stacks 0E42, instance]
instance instFiniteDimensional_tangentSpace :
    FiniteDimensional k (tangentSpace Λ k X) := sorry

end FlatAlgebraicSpaceCat
