/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Invertible.Annihilator
public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing.TraceElement
public import ReasLib.RingTheory.Kaehler.NoetherDifferent

@[expose] public section

open AlgebraicGeometry

universe u

namespace Algebra.RelativeDualizingModule

/-- For a universal trace element in an invertible relative dualizing module,
the annihilator of its cyclic quotient equals the Noether different. -/
theorem different_eq_noetherDifferent
    (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (τ : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (hτ : TraceElement.IsUniversal A B' B h_quasiFinite h_open τ)
    [Module.Invertible B (RelativeDualizingModule.of A B' B h_quasiFinite h_open)] :
    Module.annihilator B
        (RelativeDualizingModule.of A B' B h_quasiFinite h_open ⧸
          Submodule.span B {τ}) =
      KaehlerDifferential.noetherDifferent A B := sorry

end Algebra.RelativeDualizingModule
