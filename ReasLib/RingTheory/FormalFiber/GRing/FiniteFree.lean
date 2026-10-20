module

public import ReasLib.RingTheory.FormalFiber.GRing
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Detecting G-rings by finite-free extensions

@stack 07PQ

This file records the finite-free formal-fiber criterion for a Noetherian ring to be a G-ring.
-/

universe u v

namespace IsGRing

/-- Lemma 15.50.4: a Noetherian ring is a G-ring exactly when every finite-free algebra over it
has regular formal fibers. -/
@[stacks 07PQ "finite-free formal-fiber criterion"]
theorem iff_forall_finiteFree_formalFibers
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
        (p q : PrimeSpectrum S), q.asIdeal ≤ p.asIdeal →
          IsRegularRing (q.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p)) := sorry

end IsGRing
