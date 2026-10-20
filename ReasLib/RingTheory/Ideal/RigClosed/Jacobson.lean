module

public import Mathlib.RingTheory.Jacobson.Ring
public import ReasLib.RingTheory.Ideal.RigClosed
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Contracting rig-closed primes along Jacobson special fibers
-/

@[expose] public section

universe u v

/-- An adic, topologically finite-type homomorphism of Noetherian adic rings
contracts rig-closed ideals to rig-closed ideals if the source has a Jacobson
quotient by an ideal of definition. -/
theorem Ideal.IsRigClosed.comap_of_isJacobsonRing {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    [IsJacobsonRing (A ⧸ I)] :
    (q.comap φ).IsRigClosed :=
  sorry
