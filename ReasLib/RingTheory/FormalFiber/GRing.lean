/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.Geometric.Regular
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.QuasiFinite
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

/-!
# G-rings as rings with geometrically regular formal fibers

@stack 07PP
@stack 07GH
@stack 07PN

This file connects the ring-map definition of a `G`-ring to the reusable `P`-ring formal-fiber
framework.  The bridge is shared infrastructure rather than a Chapter 15 specialization.
-/

open IsLocalRing

universe u

namespace IsGRing

namespace QuasiFiniteAt

/-- Lemma 15.50.3 (1): quasi-finiteness at a target prime transfers geometric regularity from
the corresponding source formal fiber. -/
@[stacks 07PP "(1), quasi-finite transfer of a formal fiber"]
theorem formalFiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (p q : PrimeSpectrum R) (p' q' : PrimeSpectrum S)
    (hp : PrimeSpectrum.comap (algebraMap R S) p' = p)
    (hq : PrimeSpectrum.comap (algebraMap R S) q' = q)
    (hqp' : q'.asIdeal ≤ p'.asIdeal) [Algebra.QuasiFiniteAt R p'.asIdeal]
    (h_regular : Algebra.IsGeometricallyRegular q.asIdeal.ResidueField
      (q.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p))) :
    Algebra.IsGeometricallyRegular q'.asIdeal.ResidueField
      (q'.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p')) := sorry

/-- Lemma 15.50.3 (2): quasi-finiteness at a target prime transfers geometric regularity of all
formal fibers of the corresponding source localization. -/
@[stacks 07PP "(2), quasi-finite transfer of formal fibers"]
theorem formalFibers
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (p : PrimeSpectrum R) (p' : PrimeSpectrum S)
    (hp : PrimeSpectrum.comap (algebraMap R S) p' = p)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (h_regular : FieldAlgebraProperty.geometricallyRegular.HoldsOnFormalFibers
      (Localization.AtPrime p.asIdeal)) :
    FieldAlgebraProperty.geometricallyRegular.HoldsOnFormalFibers
      (Localization.AtPrime p'.asIdeal) := sorry

end QuasiFiniteAt

/-- A ring is a `G`-ring exactly when it is a `P`-ring for geometric regularity. -/
@[stacks 07GH "G-rings as P-rings"]
theorem iff_isPRing (R : Type u) [CommRing R] :
    IsGRing R ↔ IsPRing FieldAlgebraProperty.geometricallyRegular R := sorry

/-- A Noetherian local ring is a `G`-ring exactly when all its formal fibers are geometrically
regular. -/
@[stacks 07GH "local G-ring formal fibers"]
theorem iff_holdsOnFormalFibers (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    IsGRing A ↔ FieldAlgebraProperty.geometricallyRegular.HoldsOnFormalFibers A := sorry

/-- A Noetherian ring is a `G`-ring exactly when every prime-pair formal fiber is geometrically
regular. -/
@[stacks 07PN "prime-pair criterion for G-rings"]
theorem iff_forall_primePair (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ p q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal →
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField
          (q.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p)) := sorry

/-- Lemma 15.50.3 (3): a quasi-finite finite-type algebra over a `G`-ring is a `G`-ring.  The
source `G`-ring is explicit because the base ring cannot be recovered from the target alone. -/
@[stacks 07PP "(3), quasi-finite extension of a G-ring"]
theorem of_quasiFinite
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]
    (hR : IsGRing R) : IsGRing S := sorry

end IsGRing
