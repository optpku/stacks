/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime
public import ReasLib.RingTheory.Henselian.QuasiFinite
public import ReasLib.RingTheory.RingHom.Local.Residue
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Quasi-finite at-prime base change of strict henselizations

The finite comparison statement is layered over the strict-henselization
at-prime base-change API.  Its only noncanonical datum is an explicit local
comparison map, so it neither selects a comparison from a universal property
nor installs an algebra instance globally.

@stack 05WR
-/

universe u v w x

namespace IsStrictHenselizationOf.BaseChange.AtPrime

variable {R : Type u} {S : Type v} {Rsh : Type w} {Ssh : Type x}
variable [hCommR : CommRing R] [hCommS : CommRing S]
variable [hCommRsh : CommRing Rsh] [hCommSsh : CommRing Ssh]
variable [hRS : Algebra R S] [hRRsh : Algebra R Rsh] [hRSsh : Algebra R Ssh]
variable (p : Ideal R) [hp : p.IsPrime]
variable (q : Ideal S) [hq : q.IsPrime] [hLiesOver : q.LiesOver p]
variable [hRpRsh : Algebra (Localization.AtPrime p) Rsh]
variable [hRsh : IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable [hRpSsh : Algebra (Localization.AtPrime p) Ssh]
variable [hSqSsh : Algebra (Localization.AtPrime q) Ssh]
variable [hSsh : IsStrictHenselizationOf (Localization.AtPrime q) Ssh]
variable [hRpSq : Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRRsh : IsScalarTower R (Localization.AtPrime p) Rsh]
variable [hTowerRSsh : IsScalarTower R (Localization.AtPrime p) Ssh]
variable [hTowerRpSqSsh :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh]

include hRS hRRsh hRSsh hLiesOver hRsh hSsh hAtPrimeAlgebra
  hTowerRRsh hTowerRSsh hTowerRpSqSsh

namespace QuasiFiniteAt

/-- Lemma 10.156.3, tag `05WR`: if `R → S` is finite type and quasi-finite
at `q`, every explicit local comparison from a strict henselization of
`Localization.AtPrime p` to a strict henselization of
`Localization.AtPrime q` is finite.  The comparison remains input data rather
than a globally selected map. -/
@[stacks 05WR "quasi-finite strict henselization base change"]
theorem comparison_finite
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rsh) (B := Ssh))
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    RingHom.Finite comparison.hom.toRingHom := sorry

/-- Lemma 10.156.3, tag `05WR`: if `R → S` is finite type and quasi-finite
at `q`, the canonical residue-field map induced by every explicit local
comparison from a strict henselization of `Localization.AtPrime p` to a strict
henselization of `Localization.AtPrime q` is purely inseparable.  The map is
`comparison.residueFieldMap`, so no residue-field algebra structure is
installed as an ambient instance. -/
@[stacks 05WR "purely inseparable residue map of quasi-finite strict henselization base change"]
theorem residueFieldMap_isPurelyInseparable
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rsh) (B := Ssh))
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    comparison.residueFieldMap.IsPurelyInseparable := sorry

/-- Lemma 10.156.3, tag `05WR`: under finite-type quasi-finiteness at `q`,
the residue-field map induced by every explicit strict-henselization
comparison is finite and purely inseparable.  This packages the two source
properties on the canonical residue-field map without introducing an ambient
residue-field algebra instance. -/
@[stacks 05WR "finite purely inseparable residue map of quasi-finite strict henselization base change"]
theorem residueFieldMap_finitePurelyInseparable
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rsh) (B := Ssh))
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    RingHom.ResidueField.FinitePurelyInseparable
      comparison.hom.toRingHom comparison.isLocal := sorry

end QuasiFiniteAt

end IsStrictHenselizationOf.BaseChange.AtPrime
