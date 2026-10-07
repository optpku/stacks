module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A nontrivial commutative ring has disconnected prime spectrum exactly when it is
isomorphic to a product of two nontrivial commutative rings. -/
@[stacks 02DG]
theorem not_connectedSpace_iff_exists_ringEquiv_prod {A : Type u} [CommRing A] [Nontrivial A] :
    ¬ ConnectedSpace (PrimeSpectrum A) ↔
      ∃ (B C : Type u) (_ : CommRing B) (_ : CommRing C) (_ : Nontrivial B) (_ : Nontrivial C),
        Nonempty (A ≃+* B × C) := sorry

end PrimeSpectrum
