/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.Ideal.RigClosed
public import ReasLib.RingTheory.Topology.Adic.Etale
import Mathlib.Tactic.CrossRefAttribute

/-!
# Contraction of rig-closed primes along étale special fibers
-/

@[expose] public section

universe u v

/-- An adic, topologically finite type, flat homomorphism of Noetherian adic
rings with an étale defining quotient identifies a rig-closed prime with
the extension of its rig-closed contraction after localization at that prime. -/
@[stacks 0GGI]
theorem Ideal.IsRigClosed.comap_map_eq_map_atPrime {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (h_etale : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale)
    (q : Ideal B) [q.IsRigClosed] [(q.comap φ).IsRigClosed] :
    Ideal.map ((algebraMap B (Localization.AtPrime q)).comp φ) (q.comap φ) =
      Ideal.map (algebraMap B (Localization.AtPrime q)) q :=
  sorry
