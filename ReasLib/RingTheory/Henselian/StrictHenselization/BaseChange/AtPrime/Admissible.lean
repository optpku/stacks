/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.QuasiFinite
public import ReasLib.RingTheory.RingHom.FiniteType.IndQuasiFinite

@[expose] public section

/-!
# Admissible strict-henselization base change at a prime

This leaf records the four alternatives under which the strict-henselization
base-change comparison at a prime has the required residue-field behavior.
The condition depends only on one map and its two primes, not on a later
tensor-product diagram.

@stack 0GIP
-/

universe u v

namespace IsStrictHenselizationOf.BaseChange.AtPrime

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (pA : Ideal A) [pA.IsPrime]
variable (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]

/-- Tag 0GIP: the four source-faithful alternatives for strict-henselization
base change at `pB`.  The first three retain the finite-type stage condition
that the source's quasi-finite terminology requires; Mathlib's core
quasi-finite and ind-quasi-finite predicates do not record that additional
stage condition. -/
@[stacks 0GIP "admissibility alternatives for strict-henselization base change"]
inductive IsAdmissible : Prop
  /-- `A → B` is finite type and quasi-finite at `pB`. -/
  | quasiFiniteAt (h : Algebra.FiniteType.QuasiFiniteAt A B pB) :
      IsAdmissible
  /-- `B` is a filtered colimit of finite-type quasi-finite `A`-algebras. -/
  | indQuasiFinite (h : RingHom.FiniteType.IndQuasiFinite (algebraMap A B)) :
      IsAdmissible
  /-- `B_pB` is a filtered colimit of finite-type quasi-finite
  `A_pA`-algebras. -/
  | localizedIndQuasiFinite
      (h : RingHom.FiniteType.IndQuasiFinite
        (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA))) :
      IsAdmissible
  /-- `B` is integral over `A`. -/
  | integral (h : Algebra.IsIntegral A B) : IsAdmissible

end IsStrictHenselizationOf.BaseChange.AtPrime
