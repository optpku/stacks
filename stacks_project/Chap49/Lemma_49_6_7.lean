/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing.TraceElement
public import stacks_project.Chap49.Definition_49_4_1_TraceElement

@[expose] public section

open AlgebraicGeometry

universe u

namespace Algebra.RelativeDualizingModule

/- Lemma 49.6.7 (1): for a chosen finite-model presentation `A → B' → B` of a
flat quasi-finite homomorphism of Noetherian rings, evaluation at a trace element
after the isomorphism from the annihilator `J` to `Module.Dual B ω_{B/A}` agrees
with multiplication `J → B`. -/
@[stacks 0BVT] #check
  (Algebra.RelativeDualizingModule.noetherPairing_flip_apply_traceElement :
    ∀ (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B]
      [IsScalarTower A B' B] [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (tau : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
      (h_tau : TraceElement.IsUniversal A B' B h_quasiFinite h_open tau)
      (xi : (KaehlerDifferential.ideal A B).annihilator),
      (noetherPairing A B' B h_quasiFinite h_open).flip xi tau =
        Algebra.TensorProduct.lmul' A xi)

/- Lemma 49.6.7 (2): for a chosen finite-model presentation `A → B' → B` of a
flat quasi-finite homomorphism of Noetherian rings, the Noether different is the
image of evaluation at the trace element on `Module.Dual B ω_{B/A}`. -/
@[stacks 0BVT] #check
  (Algebra.RelativeDualizingModule.noetherDifferent_eq_range_eval_traceElement :
    ∀ (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B]
      [IsScalarTower A B' B] [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (tau : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
      (h_tau : TraceElement.IsUniversal A B' B h_quasiFinite h_open tau),
      KaehlerDifferential.noetherDifferent A B =
        (Module.Dual.eval B
          (RelativeDualizingModule.of A B' B h_quasiFinite h_open) tau).range)

end Algebra.RelativeDualizingModule
