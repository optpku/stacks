/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Transitivity

@[expose] public section

open AlgebraicGeometry

universe u

/- This compatibility check keeps the base-ring action visible to source-facing consumers. -/
#check
  (@Algebra.RelativeDual.relativeDualizingBaseModule :
    ∀ (R S T : Type u)
      [CommRing R] [CommRing S] [CommRing T]
      [IsNoetherianRing R] [IsNoetherianRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite R T) [Module.Finite R S]
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S T)))),
      Module R
        (Algebra.RelativeDualizingModule.of R S T h_quasiFinite h_open))
