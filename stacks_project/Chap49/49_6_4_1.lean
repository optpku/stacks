/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing

@[expose] public section

open AlgebraicGeometry

universe u v

/- 49.6.4.1: for a quasi-finite homomorphism `A → B` of Noetherian rings and a
chosen finite model `A → B' → B` inducing an open immersion on spectra, there is
a canonical `B`-bilinear pairing `ω_{B/A} × J → B`, where `J` is the annihilator
of the diagonal ideal. -/
@[stacks 0BVQ] #check
  (Algebra.RelativeDualizingModule.noetherPairing :
    (A : Type u) → (B' B : Type v) →
    [CommRing A] → [CommRing B'] → [CommRing B] →
    [IsNoetherianRing A] → [IsNoetherianRing B] →
    [Algebra A B'] → [Algebra B' B] → [Algebra A B] →
    [IsScalarTower A B' B] →
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) →
    [Module.Finite A B'] →
    (h_open : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) →
    Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₗ[B]
      ((KaehlerDifferential.ideal A B).annihilator →ₗ[B] B))
