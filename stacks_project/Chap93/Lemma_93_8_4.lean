/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Smooth

/-!
# Vanishing of `T Def_P` for a smooth `k`-algebra

In Example 93.8.1, if `P` is a smooth `k`-algebra, then the tangent space of
the residue-fibre slice `Def_P` consists of the single isomorphism class of
the trivial dual-number deformation `P[ε]`.
-/

public section

universe u

/- Lemma 93.8.4
In Example 93.8.1 let `P` be a smooth `k`-algebra. Then `T Def_P = (0)`. -/
@[stacks 0DZL] #check (FlatAlgebraCat.eq_trivialTangent :
  ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (P : Type u) [CommRing P] [Algebra k P] [Algebra.Smooth k P]
    (x : CategoryTheory.Functor.tangentSpace (FlatAlgebraCat.deformationForget Λ k P)),
    x = FlatAlgebraCat.trivialTangent Λ k P)
