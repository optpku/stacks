/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.Tensor
public import ReasLib.RingTheory.Localization.AtPrime.ResidueField

@[expose] public section

/-!
# At-prime specialization of strict-henselization tensor base change

This leaf is only the localization adapter for the neutral
`IsStrictHenselizationOf.BaseChange.Tensor` owner.  It keeps the source
statement's ideal-level residue-field hypothesis while exposing the same
explicit comparison and named carrier/algebra.  No chapter is imported and no
localization algebra instance is installed by this wrapper.

@stack 0C2Z
-/

universe u v w x y

namespace IsStrictHenselizationOf.BaseChange.AtPrime.Tensor

variable {R : Type u} {S : Type v} {Rph : Type w} {Rpsh : Type x} {Sqh : Type y}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hLocalAtPrime : IsLocalHom
  (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))]
variable [CommRing Rph]
variable [Algebra (Localization.AtPrime p) Rph]
variable [hRph : IsHenselizationOf (Localization.AtPrime p) Rph]
variable [CommRing Rpsh] [Algebra Rph Rpsh]
variable [hRpsh : IsStrictHenselizationOf Rph Rpsh]
variable [CommRing Sqh] [Algebra (Localization.AtPrime q) Sqh]
variable [hSqh : IsHenselizationOf (Localization.AtPrime q) Sqh]
variable [Algebra (Localization.AtPrime p) Sqh]
variable [hTower :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Sqh]

include hAtPrimeAlgebra hLocalAtPrime hRph hRpsh hSqh hTower in
/-- Stacks Lemma 10.155.13 (tag `0C2Z`) in prime-local form: if the map of
prime residue fields for `p ⊂ q` is bijective, an explicit local comparison
between the two henselizations yields a strict henselization of
`Localization.AtPrime q` on the named tensor carrier. -/
@[stacks 0C2Z "at-prime strict henselization tensor base change"]
theorem isStrict
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := Rph) (B := Sqh))
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (q.over_def p))) :
    @IsStrictHenselizationOf (Localization.AtPrime q) _ _
      (IsStrictHenselizationOf.BaseChange.Tensor.carrier
        (A := Localization.AtPrime p) (Ah := Rph) (Ash := Rpsh) (Bh := Sqh)
        comparison) _
      (IsStrictHenselizationOf.BaseChange.Tensor.algebra
        (A := Localization.AtPrime p) (B := Localization.AtPrime q)
        (Ah := Rph) (Ash := Rpsh) (Bh := Sqh) comparison) := sorry

end IsStrictHenselizationOf.BaseChange.AtPrime.Tensor
