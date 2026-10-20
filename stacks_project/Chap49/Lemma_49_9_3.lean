/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.NoetherDifferent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 49.9.3: on a compatible affine presentation of a flat quasi-finite
morphism of Noetherian schemes, invertibility of the relative dualizing module
identifies the different ideal sheaf with the ideal sheaf of the Noether different. -/
@[stacks 0BW6] #check
  (Algebra.RelativeDualizingModule.differentIdealSheaf_eq_noetherDifferent :
    ∀ (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B]
      [IsScalarTower A B' B] [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (τ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open)
      (hτ : Algebra.RelativeDualizingModule.TraceElement.IsUniversal
        A B' B h_quasiFinite h_open τ)
      [Module.Invertible B
        (Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open)],
      Scheme.idealSheafDataOfIdealOnSpec
          (Module.annihilator B
            (Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open ⧸
              Submodule.span B {τ})) =
        Scheme.idealSheafDataOfIdealOnSpec
          (KaehlerDifferential.noetherDifferent A B))
