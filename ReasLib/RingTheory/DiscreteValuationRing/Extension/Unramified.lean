/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Normal.Closure
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Ideal IsLocalRing Algebra

/-!
# Closure properties of unramified DVR field extensions

This leaf owns the tower, normal-closure, and common-overfield API for
`DVR.Field.IsUnramified`.  The fraction field is an explicit model `K`, so consumers do not have
to identify it definitionally with `FractionRing A`.

@stack 0EXR
@stack 0EXS
-/

universe u v w x

namespace DVR.Field.IsUnramified

section Tower

variable {A : Type u} {K : Type v} {L : Type w} {M : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
variable [IsScalarTower A K M] [IsScalarTower K L M]
variable [FiniteDimensional K L] [FiniteDimensional L M]
variable [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

/-- Lemma 15.112.8 (current Stacks Lemma 15.113.8, tag `0EXR`), clause (1):
unramifiedness descends to an intermediate field in a tower of finite separable extensions. -/
@[stacks 0EXR "unramifiedness descends in a finite separable tower"]
theorem ofTower (hM : IsUnramified A K M) :
    IsUnramified A K L := sorry

-- Proof strategy: for a maximal branch of `integralClosure A L`, choose a maximal branch of
-- `integralClosure A M` above it using the integral-closure tower lying-over API.  Apply `hM` at
-- the top branch, then descend residue-field separability and use multiplicativity of the
-- ramification index in the tower to show that the intermediate ramification index is one.

end Tower

section NormalClosure

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The canonical normal closure inside `AlgebraicClosure L` remains unramified over the base
DVR.  This is the concrete witness used by the Galois-overfield existence theorem. -/
@[stacks 0EXR "unramified canonical normal closure"]
theorem normalClosure (hL : IsUnramified A K L) :
    IsUnramified A K (IntermediateField.normalClosure K L (AlgebraicClosure L)) := sorry

-- Proof strategy: realize the normal closure as a finite compositum of conjugate copies of `L`.
-- Transfer the branchwise residue-separability and ramification-index-one conditions along each
-- conjugate embedding, then induct over the finite compositum using the integral-closure tower
-- and common-overfield closure arguments without invoking the later Galois existence theorem.

/-- Lemma 15.112.8 (current Stacks Lemma 15.113.8, tag `0EXR`), clause (2): every
finite separable unramified extension embeds in a finite Galois extension that remains
unramified. -/
@[stacks 0EXR "unramified finite Galois overfield"]
theorem existsGaloisExtension (hL : IsUnramified A K L) :
    ∃ (M : Type w) (_ : Field M) (_ : Algebra A M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower A K M),
      IsScalarTower K L M ∧ FiniteDimensional K M ∧ IsGalois K M ∧
        IsUnramified A K M := sorry

-- Proof strategy: take `M` to be `IntermediateField.normalClosure K L (AlgebraicClosure L)`.
-- Use the canonical normal-closure algebra and scalar-tower structures, its finite-dimensional
-- and Galois instances, and `normalClosure hL` for the final unramifiedness component.

end NormalClosure

section CommonExtension

variable {A : Type u} {K : Type v} {L₁ : Type w} {L₂ : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L₁] [Algebra A L₁] [Algebra K L₁] [IsScalarTower A K L₁]
variable [Field L₂] [Algebra A L₂] [Algebra K L₂] [IsScalarTower A K L₂]
variable [FiniteDimensional K L₁] [FiniteDimensional K L₂]
variable [Algebra.IsSeparable K L₁] [Algebra.IsSeparable K L₂]

/-- Lemma 15.112.8 (current Stacks Lemma 15.113.8, tag `0EXR`), clause (3): two
finite separable unramified extensions embed in a common finite separable unramified extension. -/
@[stacks 0EXR "common finite separable unramified extension"]
theorem existsCommonExtension
    (hL₁ : IsUnramified A K L₁) (hL₂ : IsUnramified A K L₂) :
    ∃ (L : Type (max w x)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A K L),
      IsScalarTower K L₁ L ∧ IsScalarTower K L₂ L ∧ FiniteDimensional K L ∧
        Algebra.IsSeparable K L ∧ IsUnramified A K L := sorry

-- Proof strategy: embed `L₁` and `L₂` into finite Galois unramified overfields supplied by
-- `existsGaloisExtension`, place both inside a common algebraic closure, and take their finite
-- compositum.  Assemble the induced algebra and scalar-tower structures, then verify the
-- branchwise unramified conditions by the same finite-compositum argument as for normal closure.

end CommonExtension

section IntegralClosureTower

variable {A : Type u} {K : Type v} {L : Type w} {M : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
variable [IsScalarTower A L M] [IsScalarTower A K M] [IsScalarTower K L M]
variable [FiniteDimensional K L] [FiniteDimensional L M]
variable [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/-- Lemma 15.112.9 (current Stacks Lemma 15.113.9, tag `0EXS`): the local hypothesis on
`M/L` written in the canonical branch form.  For every maximal branch `m` of `B` over `A`,
every maximal branch `P` of `C` over `m` is unramified at `P` over `B`. -/
@[stacks 0EXS "local branch hypothesis in an integral-closure tower"]
def IsUnramifiedOnTower : Prop :=
  ∀ (m : Ideal B) [m.IsMaximal] [m.LiesOver (maximalIdeal A)],
    letI : Algebra B C := integralClosure.Tower.algebra (A := A) (L := L) (M := M)
    ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver m], Algebra.IsUnramifiedAt B P

/-- Lemma 15.112.9 (current Stacks Lemma 15.113.9, tag `0EXS`), branch conclusion: under the
unramifiedness hypothesis on `L/K` and the local tower hypothesis on `M/L`, each maximal branch
of the top integral closure is unramified over `A`. -/
@[stacks 0EXS "branchwise unramifiedness composes in an integral-closure tower"]
theorem atIntegralClosureTower
    (hL : IsUnramified A K L) (hM : IsUnramifiedOnTower (A := A) (L := L) (M := M))
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Algebra.IsUnramifiedAt A P := sorry

-- Proof strategy: let `m := integralClosure.Tower.under P`.  Use the tower API to obtain
-- maximality and lying-over for `m`, specialize `hL` at `m` and `hM m P`, and compose the two
-- `Algebra.IsUnramifiedAt` statements through `integralClosure.Tower.algebra` and its canonical
-- scalar-tower structure.

/-- Lemma 15.112.9 (current Stacks Lemma 15.113.9, tag `0EXS`): if `M/L/K` is a finite
separable tower, `L/K` is unramified with respect to `A`, and the localized `M/L` branches are
unramified over the intermediate integral closure, then `M/K` is unramified with respect to `A`.
The branch condition is exposed by `IsUnramifiedOnTower` so later proofs can use it directly. -/
@[stacks 0EXS "unramifiedness composes in a finite separable integral-closure tower"]
theorem ofIntegralClosureTower
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (hL : IsUnramified A K L)
    (hM : IsUnramifiedOnTower (A := A) (L := L) (M := M)) :
    IsUnramified A K M := sorry

-- Proof strategy: apply the reverse implication of
-- `DVR.Field.IsUnramified.iff_forall_isUnramifiedAt`.  For every maximal branch `P` of the top
-- integral closure, discharge the required local statement with `atIntegralClosureTower hL hM P`.

end IntegralClosureTower

end DVR.Field.IsUnramified
