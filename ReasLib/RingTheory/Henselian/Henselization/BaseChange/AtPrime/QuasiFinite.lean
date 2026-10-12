/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization.BaseChange.AtPrime
public import ReasLib.RingTheory.Henselian.Henselization.Henselian
public import ReasLib.RingTheory.Henselian.QuasiFinite

@[expose] public section

/-!
# Quasi-finite at-prime base change of henselizations

The finite comparison theorem belongs after the generic at-prime
local-target construction: its only noncanonical input is an explicit local
comparison map.  In particular, this file never selects such a map from a
universal property.

@stack 05WP
-/

universe u v w x

namespace IsHenselizationOf.BaseChange.AtPrime

variable {R : Type u} {S : Type v} {Rh : Type w} {Sh : Type x}
variable [hCommR : CommRing R] [hCommS : CommRing S]
variable [hCommRh : CommRing Rh] [hCommSh : CommRing Sh]
variable [hRS : Algebra R S] [hRRh : Algebra R Rh] [hRSh : Algebra R Sh]
variable (p : Ideal R) [hp : p.IsPrime]
variable (q : Ideal S) [hq : q.IsPrime] [hLiesOver : q.LiesOver p]
variable [hRpRh : Algebra (Localization.AtPrime p) Rh]
variable [hRh : IsHenselizationOf (Localization.AtPrime p) Rh]
variable [hRpSh : Algebra (Localization.AtPrime p) Sh]
variable [hSqSh : Algebra (Localization.AtPrime q) Sh]
variable [hSh : IsHenselizationOf (Localization.AtPrime q) Sh]
variable [hRpSq : Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRRh : IsScalarTower R (Localization.AtPrime p) Rh]
variable [hTowerRSh : IsScalarTower R (Localization.AtPrime p) Sh]
variable [hTowerRpSqSh :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Sh]

include hRS hRRh hRSh hLiesOver hRh hSh hAtPrimeAlgebra
  hTowerRRh hTowerRSh hTowerRpSqSh

namespace QuasiFiniteAt

/-- Tag 05WP: if `R → S` is finite type and quasi-finite at `q`, then every
explicit local comparison from a henselization of `Localization.AtPrime p` to
a henselization of `Localization.AtPrime q` is finite.  The comparison remains
an input rather than a globally chosen map. -/
@[stacks 05WP "quasi-finite henselization base change"]
theorem comparison_finite
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rh) (B := Sh))
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    RingHom.Finite comparison.hom.toRingHom := sorry

end QuasiFiniteAt

end IsHenselizationOf.BaseChange.AtPrime
