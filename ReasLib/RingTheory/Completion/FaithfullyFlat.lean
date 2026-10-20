module

public import ReasLib.RingTheory.Completion.Flat
public import ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum
public import ReasLib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Faithful flatness of adic completion

The main theorem is stated with the intrinsic Jacobson-radical hypothesis;
the complete-local-ring form is an immediate reusable specialization.

@stack 00MC
-/

universe u

open IsLocalRing

namespace AdicCompletion

/-- If `R` is Noetherian and `I` lies in its Jacobson radical,
the canonical map from `R` to its `I`-adic completion is faithfully flat. -/
@[stacks 00MC "faithful flatness of adic completion"]
theorem algebraMap_faithfullyFlat
    {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
    (hI : I ≤ Ring.jacobson R) :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion I R)) := sorry

/-- The maximal-ideal adic completion of a Noetherian local ring is faithfully
flat over the original ring. -/
@[stacks 00MC, stacks 0FIZ "local-ring specialization"]
theorem maximalIdeal_algebraMap_faithfullyFlat
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion (maximalIdeal R) R)) := sorry

end AdicCompletion

/-- The canonical map from a Noetherian ring to its adic completion at an
ideal contained in the Jacobson radical is faithfully flat. -/
theorem adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
    (hI : I ≤ Ring.jacobson R) :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion I R)) := sorry

/-- The canonical map from a Noetherian local ring to its maximal-ideal adic
completion is faithfully flat. -/
theorem maximalIdeal_adicCompletion_algebraMap_faithfullyFlat
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion (maximalIdeal R) R)) := sorry
