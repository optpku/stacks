/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.RigClosed

@[expose] public section

universe u v

/- The induced map on topological-nilradical quotients is the canonical reduction of a continuous ring homomorphism. -/
#check (RingHom.topologicalNilradicalQuotient :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B],
    (φ : A →+* B) → Continuous φ →
      A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B)
