/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Localization.AtPrime.LocalTarget

@[expose] public section

/-!
# At-prime base change of henselizations

This leaf records the reusable tensor-product and localization data used when
a henselization of `Localization.AtPrime p` is compared with a henselization of
`Localization.AtPrime q` above it.
The comparison is always explicit: no map is selected from the henselization
universal property.  Tensor-product and local-target constructions delegate
to their neutral ReasLib owners.

@stack 08HU
-/

universe u v w x

namespace IsHenselizationOf.BaseChange.AtPrime.Tensor

variable {R : Type u} {S : Type v} {Rh : Type w} {Sh : Type x}
variable [CommRing R] [CommRing S] [CommRing Rh] [CommRing Sh]
variable [Algebra R S] [Algebra R Rh] [Algebra R Sh]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [hLiesOver : q.LiesOver p]
variable [Algebra (Localization.AtPrime p) Rh]
variable [hRh : IsHenselizationOf (Localization.AtPrime p) Rh]
variable [Algebra (Localization.AtPrime p) Sh]
variable [Algebra (Localization.AtPrime q) Sh]
variable [hSh : IsHenselizationOf (Localization.AtPrime q) Sh]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRRh : IsScalarTower R (Localization.AtPrime p) Rh]
variable [hTowerRSh : IsScalarTower R (Localization.AtPrime p) Sh]
variable [hTowerRpSqSh :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Sh]

include hLiesOver hRh hSh hAtPrimeAlgebra hTowerRRh hTowerRSh hTowerRpSqSh in
/-- Lemma 10.155.8 (Tag 08HU): the target henselization `Sh` is a
henselization of the localization of `Rh ⊗[R] S` at the prime selected by the
explicit local comparison and the canonical map
`S → Localization.AtPrime q → Sh`.  The algebra
structure in the conclusion is the named `localizedAlgebra`, so no global
instance is selected. -/
@[stacks 08HU]
theorem isHenselizationOf
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rh) (B := Sh)) :
    @IsHenselizationOf
      (Localization.AtPrime
        (Localization.AtPrime.LocalTarget.tensorPrime (p := p) (q := q) comparison).asIdeal)
      _ _ Sh _
        (Localization.AtPrime.LocalTarget.localizedAlgebra
          (p := p) (q := q) comparison) := sorry

end IsHenselizationOf.BaseChange.AtPrime.Tensor
