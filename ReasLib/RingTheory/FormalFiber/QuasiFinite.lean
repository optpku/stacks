/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws
public import ReasLib.RingTheory.FormalFiber.PRing

@[expose] public section

/-!
# Quasi-finite transfer of formal-fiber properties

The statements distinguish a local ring having property `P` on its own formal fibers from that
local ring being a `P`-ring.  This distinction is essential for the primewise transfer theorem.

@stack 0BIT
-/

universe u

namespace FieldAlgebraProperty.QuasiFiniteAt

variable (P : FieldAlgebraProperty.{u, u})
variable [P.EssFiniteTypeBaseChange] [P.IsLocal]
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]

/-- A quasi-finite map at `p'` transfers property `P` from the corresponding source formal fiber
to a target formal fiber. -/
@[stacks 0BIT "(1)"]
theorem formalFiber (p q : PrimeSpectrum R) (p' q' : PrimeSpectrum S)
    (hp : PrimeSpectrum.comap (algebraMap R S) p' = p)
    (hq : PrimeSpectrum.comap (algebraMap R S) q' = q)
    (hqp' : q'.asIdeal ≤ p'.asIdeal) [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : P q.asIdeal.ResidueField
      (q.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p))) :
    P q'.asIdeal.ResidueField
      (q'.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p')) := sorry

/-- A quasi-finite map at `p'` transfers property `P` on all formal fibers of the source prime
localization to all formal fibers of the target prime localization. -/
@[stacks 0BIT "(2)"]
theorem formalFibers (p : PrimeSpectrum R) (p' : PrimeSpectrum S)
    (hp : PrimeSpectrum.comap (algebraMap R S) p' = p)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : P.HoldsOnFormalFibers (Localization.AtPrime p.asIdeal)) :
    P.HoldsOnFormalFibers (Localization.AtPrime p'.asIdeal) := sorry

end FieldAlgebraProperty.QuasiFiniteAt

namespace IsPRing

/-- A finite-type quasi-finite algebra over a `P`-ring is again a `P`-ring. -/
@[stacks 0BIT "(3)"]
theorem of_quasiFinite (P : FieldAlgebraProperty.{u, u})
    [P.EssFiniteTypeBaseChange] [P.IsLocal]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]
    (hR : IsPRing P R) : IsPRing P S := sorry

end IsPRing
