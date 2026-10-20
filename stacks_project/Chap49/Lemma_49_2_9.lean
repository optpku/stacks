/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Flat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.RelativeDual

universe u

/- Lemma 49.2.9: for a flat quasi-finite homomorphism `A → B` of Noetherian
rings, the relative dualizing module `ω_{B/A}` is flat as an `A`-module. -/
@[stacks 0BVE] #check
  (Algebra.RelativeDualizingModule.flat :
    ∀ (A B' B : Type u)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))),
      Module.Flat A
        (Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open))
