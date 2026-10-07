module

public import ReasLib.RingTheory.RingHom.Local.AtPrime
public import ReasLib.RingTheory.Smooth.Adic.Basic
public import ReasLib.RingTheory.Smooth.AtPrime
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness at a Prime and Adic Formal Smoothness

This leaf compares smoothness at a target prime with formal smoothness of the canonical map on
local rings for the target maximal-ideal-adic topology.

@stack 07VH
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Algebra

/-- Lemma 15.38.6 (Stacks `07VH`): for a finite-type algebra over a Noetherian ring,
smoothness at `q` is equivalent to maximal-ideal-adic formal smoothness of the induced map on
local rings. -/
@[stacks 07VH "smoothness at a prime via adic formal smoothness"]
theorem smoothAtPrime_iff_formally_smooth_for_adic_localized_map
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] (q : PrimeSpectrum B) :
    SmoothAtPrime A B q ↔
      (RingHom.localRingHomAt (algebraMap A B) q).formally_smooth_for_adic
        (maximalIdeal (Localization.AtPrime q.asIdeal)) := sorry

end Algebra
