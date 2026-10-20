/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap49.«49_2_0_1_RelativeDualizingModule»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

/- 49.2.0.1: for a chosen finite factorization `A → B' → B` of a quasi-finite map of
Noetherian rings, with `Spec B → Spec B'` an open immersion, the relative dualizing module
`omega_{B/A}` is `Module.Dual A B' ⊗[B'] B`. -/
@[stacks 0BSZ] #check (Algebra.RelativeDualizingModule.of_eq :
  ∀ (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))),
    Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open =
      @ModuleCat.of B _ (Algebra.DualModule.of A B' ⊗[B'] B) _ TensorProduct.Right.module)
