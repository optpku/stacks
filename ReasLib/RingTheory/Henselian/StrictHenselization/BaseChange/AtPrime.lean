/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Localization.AtPrime.LocalTarget
public import ReasLib.RingTheory.RingHom.Local.Residue

@[expose] public section

/-!
# At-prime base change of strict henselizations

This leaf places the strict-henselization conclusion over the neutral
at-prime local-target construction.  A comparison map is explicit input:
the module records no chosen comparison and introduces no global algebra
instance for the localized tensor product.

@stack 08HV
-/

universe u v w x

namespace IsStrictHenselizationOf.BaseChange.AtPrime.Tensor

open IsLocalRing

variable {R : Type u} {S : Type v} {Rsh : Type w} {Ssh : Type x}
variable [CommRing R] [CommRing S] [CommRing Rsh] [CommRing Ssh]
variable [Algebra R S] [Algebra R Rsh] [Algebra R Ssh]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [hLiesOver : q.LiesOver p]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [hRsh : IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable [Algebra (Localization.AtPrime p) Ssh]
variable [Algebra (Localization.AtPrime q) Ssh]
variable [hSsh : IsStrictHenselizationOf (Localization.AtPrime q) Ssh]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRRsh : IsScalarTower R (Localization.AtPrime p) Rsh]
variable [hTowerRSsh : IsScalarTower R (Localization.AtPrime p) Ssh]
variable [hTowerRpSqSsh :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh]

include hLiesOver hRsh hSsh hAtPrimeAlgebra hTowerRRsh hTowerRSsh hTowerRpSqSsh in
/-- Tag 08HV: given an explicit local comparison from a strict henselization
of `Localization.AtPrime p` to a strict henselization of
`Localization.AtPrime q`, the latter is a strict henselization of the
localization of `Rsh ⊗[R] S` at its induced tensor prime.  The conclusion
uses `Localization.AtPrime.LocalTarget.localizedAlgebra` as an explicit
algebra owner; it never selects a comparison map or a global localized
algebra instance. -/
@[stacks 08HV]
theorem isStrictHenselizationOf
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rsh) (B := Ssh)) :
    @IsStrictHenselizationOf
      (Localization.AtPrime
        (Localization.AtPrime.LocalTarget.tensorPrime (p := p) (q := q) comparison).asIdeal)
      _ _ Ssh _
        (Localization.AtPrime.LocalTarget.localizedAlgebra
          (p := p) (q := q) comparison) := sorry

include hLiesOver hRsh hSsh hAtPrimeAlgebra
  hTowerRRsh hTowerRSsh hTowerRpSqSsh in
/-- Tag 0C2Z: an explicit comparison with bijective residue-field map gives
the strong tensor base-change criterion.  This is separate from the 08HV
strict-henselization comparison, whose compatible residue map need not be
bijective. -/
@[stacks 0C2Z "localized-tensor strict-henselization criterion"]
theorem isStrict_of_bijectiveComparison
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rsh) (B := Ssh))
    (hκ : Function.Bijective comparison.residueFieldMap) :
    @IsStrictHenselizationOf
      (Localization.AtPrime
        (Localization.AtPrime.LocalTarget.tensorPrime
          (p := p) (q := q) comparison).asIdeal)
      _ _ Ssh _
      (Localization.AtPrime.LocalTarget.localizedAlgebra
        (p := p) (q := q) comparison) := sorry

end IsStrictHenselizationOf.BaseChange.AtPrime.Tensor
