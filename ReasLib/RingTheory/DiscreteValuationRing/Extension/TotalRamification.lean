/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Totally ramified extensions of discrete valuation rings

This file owns the extension-level predicate used by the Kummer base-change API.  The
intermediate fraction field is a parameter rather than an implementation choice, so the same
predicate applies after replacing a fraction field by an isomorphic field model.

@stack 09E9
-/

universe u v w

open Ideal IsLocalRing

namespace DVR.Field

section

variable (A : Type u) (K : Type v) (L : Type w)
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- The extension `L / K` is totally ramified over the DVR `A` when the integral closure has a
unique maximal ideal above `maximalIdeal A` and the induced residue-field map is bijective.

The fraction field `K` is carried by an `IsFractionRing A K` instance instead of being fixed to
the definitional choice `FractionRing A`; this is the reusable layer for base-change statements.
-/
@[stacks 09E9 "totally ramified extension over a DVR"]
class IsTotallyRamified (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] : Prop where
  /-- Maximal ideals of the integral closure above the base maximal ideal coincide. -/
  unique_maximalIdeal (P Q : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] [Q.IsMaximal] [Q.LiesOver (maximalIdeal A)] :
      P = Q
  /-- The residue-field map at a maximal branch above the base maximal ideal is bijective. -/
  residueField_bijective (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
          (P.over_def (maximalIdeal A)))

end

namespace IsTotallyRamified

section

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- The unique-branch clause of total ramification, exposed as a named projection for downstream
branch arguments. -/
@[stacks 09E9 "totally ramified unique branch"]
theorem unique_branch (h : IsTotallyRamified A K L)
    (P Q : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] [Q.IsMaximal] [Q.LiesOver (maximalIdeal A)] :
    P = Q := sorry
-- Proof strategy: project `IsTotallyRamified.unique_maximalIdeal` from `h` at `P` and `Q`.

/-- The residue-field clause of total ramification, exposed without unfolding the class. -/
@[stacks 09E9 "totally ramified residue field"]
theorem residue_bijective (h : IsTotallyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
            (P.over_def (maximalIdeal A))) := h.residueField_bijective P

/-- The canonical residue-field algebra map of a totally ramified branch is bijective. -/
@[stacks 09E9 "totally ramified residue-field algebra map bijective"]
theorem residue_algebraMap_bijective (h : IsTotallyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    -- Local instance justification (instance diamond): the residue algebra depends on the chosen
    -- lying-over branch and must remain scoped to this statement.
    letI : Algebra (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P) :=
      Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P
    Function.Bijective (algebraMap (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)) := by
  exact h.residue_bijective P

/-- The residue-field algebra equivalence supplied by a totally ramified branch. -/
@[stacks 09E9 "totally ramified residue-field algebra equivalence"]
noncomputable def residueFieldAlgEquiv (h : IsTotallyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    -- Local instance justification (instance diamond): select the branch algebra only for this
    -- equivalence instead of exporting it globally.
    letI : Algebra (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P) :=
      Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P
    Ideal.ResidueField (maximalIdeal A) ≃ₐ[Ideal.ResidueField (maximalIdeal A)]
      Ideal.ResidueField P :=
  -- Local instance justification (defeq pin): install the same branch residue-field algebra as the result type so Algebra.ofId and AlgEquiv.ofBijective use that algebra.
  letI : Algebra (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P) :=
    Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P
  AlgEquiv.ofBijective (Algebra.ofId _ _) (h.residue_algebraMap_bijective P)

/-- The residue-field equivalence supplied by a totally ramified branch. -/
@[stacks 09E9 "totally ramified residue-field equivalence"]
noncomputable def residueFieldEquiv (h : IsTotallyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Ideal.ResidueField (maximalIdeal A) ≃+* Ideal.ResidueField P :=
  -- Local instance justification (instance diamond): recover the same branch algebra used by the
  -- canonical `AlgEquiv` only while projecting its underlying ring equivalence.
  letI : Algebra (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P) :=
    Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P
  (h.residueFieldAlgEquiv P).toRingEquiv

/-- The underlying map of the canonical residue-field equivalence is the lying-over residue map. -/
@[simp, stacks 09E9 "totally ramified residue-field equivalence application"]
theorem residueFieldEquiv_apply (h : IsTotallyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)]
    (x : Ideal.ResidueField (maximalIdeal A)) :
    h.residueFieldEquiv P x =
      Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
        (P.over_def (maximalIdeal A)) x := rfl

/-- The unique-branch and residue-bijection clauses bundled by total ramification. -/
@[stacks 09E9 "totally ramified branch specification"]
theorem spec (h : IsTotallyRamified A K L) :
    (∀ (P Q : Ideal (integralClosure A L)) [P.IsMaximal]
        [P.LiesOver (maximalIdeal A)] [Q.IsMaximal]
        [Q.LiesOver (maximalIdeal A)], P = Q) ∧
      (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
        [P.LiesOver (maximalIdeal A)],
        Function.Bijective
          (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
            (P.over_def (maximalIdeal A)))) := sorry
-- Proof strategy: pair `h.unique_branch` and `h.residue_bijective`, retaining each branch's
-- maximality and lying-over instances in the two quantified components.

/-- Total ramification is equivalent to a unique maximal branch and bijective residue map. -/
@[stacks 09E9 "totally ramified branch characterization"]
theorem iff_forall :
    IsTotallyRamified A K L ↔
      (∀ (P Q : Ideal (integralClosure A L)) [P.IsMaximal]
          [P.LiesOver (maximalIdeal A)] [Q.IsMaximal]
          [Q.LiesOver (maximalIdeal A)], P = Q) ∧
        (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
          [P.LiesOver (maximalIdeal A)],
          Function.Bijective
            (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
              (P.over_def (maximalIdeal A)))) := sorry
-- Proof strategy: use `IsTotallyRamified.spec` forward; backward, construct the class by assigning
-- the two quantified hypotheses to `unique_maximalIdeal` and `residueField_bijective`.

/-- For a finite separable totally ramified extension, the ramification index at its unique
maximal branch is the field degree. -/
@[stacks 09E9, stacks 09F0 "totally ramified index equals field degree"]
theorem ramificationIdx_eq_finrank [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : IsTotallyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    P.ramificationIdx A = Module.finrank K L := sorry
-- Proof strategy: specialize the ramification-inertia degree formula to `maximalIdeal A`; use
-- `h.unique_branch` to collapse the prime-fiber sum to `P`, and use `h.residue_bijective P` to
-- identify `P.inertiaDeg A` with `1`, leaving the stated ramification-index equality.

end

end IsTotallyRamified

/-- The identity extension of the fraction field is totally ramified over a DVR.

The specialization is kept as a named instance in ReasLib so downstream users do not need to
rebuild the integral-closure and residue-field identifications locally. -/
@[stacks 09E9 "totally ramified identity fraction-field extension"]
instance IsTotallyRamified.of_fractionRing (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    IsTotallyRamified A (FractionRing A) (FractionRing A) := sorry
-- Proof strategy: identify `integralClosure A (FractionRing A)` with `A` by integrally closedness
-- of the DVR; the unique branch is `maximalIdeal A`, and the resulting residue map is the identity,
-- hence bijective.

end DVR.Field
