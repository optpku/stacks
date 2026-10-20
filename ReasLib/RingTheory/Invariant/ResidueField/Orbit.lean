/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.LocalRing.ResidueField.LiesOver

@[expose] public section

/-!
# Residue-field transport along an invariant orbit

This leaf keeps Mathlib's canonical residue-field equivalence and packages
the orbit specialization used by invariant extensions.  The residue-field
algebra structures are pair-dependent, so they remain scoped in the result
instead of competing global instances.
@stack 09ED
-/

open scoped Pointwise

universe u v w

namespace Ideal.ResidueField.Invariant

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type w} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The comap equality needed for the canonical residue-field equivalence
induced by an invariant orbit. -/
@[stacks 09ED "comap bridge for an invariant residue-field orbit"]
theorem comap_eq_of_smul_eq
    (p : Ideal A) [p.IsPrime]
    (q q' : Ideal B) [q.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [q'.LiesOver p]
    (g : G) (h : g • q = q') :
    q = q'.comap (MulSemiringAction.toAlgEquiv A B g).toRingHom := sorry
-- Proof strategy: rewrite pointwise ideal transport with
-- `Ideal.pointwise_smul_eq_comap` and use `h`; cancellation by the inverse algebra equivalence
-- converts the equality `g • q = q'` into the displayed comap equality.

/-- The ideal map equality underlying an invariant orbit. -/
@[stacks 09ED "map bridge for an invariant residue-field orbit"]
theorem map_eq_of_smul_eq
    (p : Ideal A) [p.IsPrime]
    (q q' : Ideal B) [q.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [q'.LiesOver p]
    (g : G) (h : g • q = q') :
    q' = q.map (MulSemiringAction.toAlgEquiv A B g).toRingHom := sorry
-- Proof strategy: apply the map-comap correspondence for the surjective ring homomorphism
-- underlying `MulSemiringAction.toAlgEquiv A B g`, then discharge the comap side with
-- `comap_eq_of_smul_eq`.

/-- An element carrying one prime ideal to another induces an algebra
equivalence of their residue fields over the base residue field. -/
@[stacks 09ED "residue-field equivalence induced by an invariant orbit"]
noncomputable def algEquivOfSmulEq
    (p : Ideal A) [p.IsPrime]
    (q q' : Ideal B) [q.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [q'.LiesOver p]
    (g : G) (h : g • q = q') :
    -- Local instance justification (defeq pin): select the source-branch residue algebra for the orbit equivalence.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    -- Local instance justification (defeq pin): select the target-branch residue algebra for the orbit equivalence.
    letI : Algebra p.ResidueField q'.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q'
    q.ResidueField ≃ₐ[p.ResidueField] q'.ResidueField :=
  let e := MulSemiringAction.toAlgEquiv A B g
  -- Local instance justification (defeq pin): use the source branch's residue algebra in the fraction-field equivalence.
  letI : Algebra p.ResidueField q.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver p q
  -- Local instance justification (defeq pin): use the target branch's residue algebra in the fraction-field equivalence.
  letI : Algebra p.ResidueField q'.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver p q'
  -- Local instance justification (defeq pin): install the source branch's quotient algebra for fraction-field transport.
  letI : Algebra (A ⧸ p) q.ResidueField :=
    Ideal.ResidueField.LiesOver.quotientAlgebra p q
  -- Local instance justification (defeq pin): install the target branch's quotient algebra for fraction-field transport.
  letI : Algebra (A ⧸ p) q'.ResidueField :=
    Ideal.ResidueField.LiesOver.quotientAlgebra p q'
  -- Local instance justification (defeq pin): install the source branch's residue scalar tower.
  letI : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_residue p q
  -- Local instance justification (defeq pin): install the source branch's quotient scalar tower.
  letI : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_quotient p q
  -- Local instance justification (defeq pin): install the target branch's residue scalar tower.
  letI : IsScalarTower (A ⧸ p) p.ResidueField q'.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_residue p q'
  -- Local instance justification (defeq pin): install the target branch's quotient scalar tower.
  letI : IsScalarTower (A ⧸ p) (B ⧸ q') q'.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_quotient p q'
  IsFractionRing.fieldEquivOfAlgEquiv p.ResidueField q.ResidueField q'.ResidueField
    (Ideal.Quotient.algEquivOfEqMap p e (map_eq_of_smul_eq p q q' g h))

/-- Residue-field separability is invariant under an invariant orbit. -/
@[stacks 09ED "separability is constant on an invariant residue-field orbit"]
theorem isSeparable_iff_of_smul_eq
    (p : Ideal A) [p.IsPrime]
    (q q' : Ideal B) [q.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [q'.LiesOver p]
    (g : G) (h : g • q = q') :
    -- Local instance justification (defeq pin): select the source branch's residue algebra for separability transport.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    -- Local instance justification (defeq pin): select the target branch's residue algebra for separability transport.
    letI : Algebra p.ResidueField q'.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q'
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔
      Algebra.IsSeparable p.ResidueField q'.ResidueField := sorry
-- Proof strategy: install the two lying-over residue-field algebra structures and apply
-- `AlgEquiv.Algebra.isSeparable_iff` to `algEquivOfSmulEq p q q' g h`.

end Ideal.ResidueField.Invariant
