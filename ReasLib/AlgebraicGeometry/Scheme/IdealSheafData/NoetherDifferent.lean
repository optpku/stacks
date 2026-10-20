/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec

@[expose] public section

open AlgebraicGeometry

universe u

namespace Algebra.RelativeDualizingModule

/-- For a universal trace element in an invertible relative dualizing module,
the associated ideal sheaf of its cyclic-quotient annihilator equals the ideal
sheaf of the Noether different. -/
theorem differentIdealSheaf_eq_noetherDifferent
    (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (τ : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (hτ : TraceElement.IsUniversal A B' B h_quasiFinite h_open τ)
    [Module.Invertible B (RelativeDualizingModule.of A B' B h_quasiFinite h_open)] :
    Scheme.idealSheafDataOfIdealOnSpec
        (Module.annihilator B
          (RelativeDualizingModule.of A B' B h_quasiFinite h_open ⧸
            Submodule.span B {τ})) =
      Scheme.idealSheafDataOfIdealOnSpec
        (KaehlerDifferential.noetherDifferent A B) := sorry

end Algebra.RelativeDualizingModule
