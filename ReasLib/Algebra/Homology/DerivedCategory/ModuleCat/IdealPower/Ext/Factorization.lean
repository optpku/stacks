/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Linear
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.StageMaps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic factorization of Ext restriction maps

This file owns the reusable statement behind Stacks Project, Lemma 15.102.2.  A
`Factorisation` retains the actual lift through the prescribed pair of adic stages;
`FactorsAt` and `EventuallyFactors` expose the corresponding single-stage and tail properties.
The degree-zero factor is concrete, and the Noetherian theorem is uniform in the target module.

@stack 0G3L
@stack 0927
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open Ideal.PowerSubmodule

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IdealPower.ExtRestriction

variable {A : Type u} [CommRing A] [HasExt (ModuleCat.{v} A)]

/-- A factorization of Ext restriction through prescribed adic stages of both variables. -/
@[stacks 0G3L "adic factorization of an Ext restriction map"]
structure Factorisation
    (I : Ideal A) (M N : ModuleCat.{v} A) (p n m : ℕ) where
  /-- The lift from ambient Ext to Ext between the prescribed adic stages. -/
  lift : Ext M N p →ₗ[A] Ext (stageObj I M n) (stageObj I N m) p
  /-- Postcomposing the lift with the target-stage inclusion is source restriction. -/
  fac :
    (subtypeExtPostcomp I (stageObj I M n) N m p).comp lift =
      subtypeExtPrecomp I M N n p

namespace Factorisation

/-- Pointwise form of the factorization equation. -/
@[simp, stacks 0G3L "pointwise adic Ext factorization equation"]
theorem fac_apply
    {I : Ideal A} {M N : ModuleCat.{v} A} {p n m : ℕ}
    (D : Factorisation I M N p n m) (x : Ext M N p) :
    subtypeExtPostcomp I (stageObj I M n) N m p (D.lift x) =
      subtypeExtPrecomp I M N n p x := by
  simpa only [LinearMap.comp_apply] using congrArg (fun f => f x) D.fac

/-- A factorization through a zero target-stage map makes source restriction zero. -/
@[stacks 0927 "zero consequence of an adic Ext factorization"]
theorem precomp_eq_zero_of_postcomp_eq_zero
    {I : Ideal A} {M N : ModuleCat.{v} A} {p n m : ℕ}
    (D : Factorisation I M N p n m)
    (h : subtypeExtPostcomp I (stageObj I M n) N m p = 0) :
    subtypeExtPrecomp I M N n p = 0 := by
  rw [← D.fac, h]
  simp

/-- The degree-zero lift is restriction of an ambient morphism to unequal adic stages. -/
@[stacks 0G3L "degree-zero adic Ext lift"]
noncomputable def degreeZeroLift
    (I : Ideal A) (M N : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    Ext M N 0 →ₗ[A] Ext (stageObj I M n) (stageObj I N m) 0 :=
  ((Ext.linearEquiv₀ :
      Ext (stageObj I M n) (stageObj I N m) 0 ≃ₗ[A]
        (stageObj I M n ⟶ stageObj I N m)).symm.toLinearMap).comp
    ((mapObjToStageLinear I M N h).comp
      (Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N)).toLinearMap)

/-- The degree-zero lift satisfies the Ext factorization equation. -/
@[stacks 0G3L "degree-zero adic Ext lift factorization"]
theorem degreeZeroLift_fac
    (I : Ideal A) (M N : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    (subtypeExtPostcomp I (stageObj I M n) N m 0).comp
        (degreeZeroLift I M N h) =
      subtypeExtPrecomp I M N n 0 := by
  ext x
  suffices
      Ext.mk₀ (mapObjToStage I (Ext.linearEquiv₀ (R := A) x) h ≫
        ModuleCat.ofHom (subtype I N m)) =
      (Ext.mk₀ (ModuleCat.ofHom (subtype I M n))).comp x (zero_add 0) by
    simpa [degreeZeroLift, subtypeExtPostcomp, subtypeExtPrecomp, mapObjToStageLinear] using this
  rw [mapObjToStage_comp_subtype]
  simpa only [Ext.mk₀_linearEquiv₀_apply] using
    (Ext.mk₀_comp_mk₀ (ModuleCat.ofHom (subtype I M n))
      (Ext.linearEquiv₀ (R := A) x)).symm

/-- The explicit degree-zero factor through a shallower target stage. -/
@[stacks 0G3L "degree-zero adic Ext factorization"]
noncomputable def degreeZero
    (I : Ideal A) (M N : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    Factorisation I M N 0 n m where
  lift := degreeZeroLift I M N h
  fac := degreeZeroLift_fac I M N h

/-- The degree-zero lift sends a morphism class to its unequal-stage restriction. -/
@[stacks 0G3L "degree-zero adic Ext factorization formula"]
theorem degreeZero_lift_mk₀
    (I : Ideal A) (M N : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) (f : M ⟶ N) :
    (degreeZero I M N h).lift (Ext.mk₀ f) = Ext.mk₀ (mapObjToStage I f h) := by
  have hf :
      (Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N)) (Ext.mk₀ f) = f := by
    apply (Ext.mk₀_bijective M N).1
    simp only [Ext.mk₀_linearEquiv₀_apply]
  have hg :
      (Ext.linearEquiv₀ :
        Ext (stageObj I M n) (stageObj I N m) 0 ≃ₗ[A]
          (stageObj I M n ⟶ stageObj I N m))
        (Ext.mk₀ (mapObjToStage I f h)) = mapObjToStage I f h := by
    apply (Ext.mk₀_bijective (stageObj I M n) (stageObj I N m)).1
    simp only [Ext.mk₀_linearEquiv₀_apply]
  change (Ext.linearEquiv₀ :
    Ext (stageObj I M n) (stageObj I N m) 0 ≃ₗ[A]
      (stageObj I M n ⟶ stageObj I N m)).symm
      (mapObjToStage I ((Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N))
        (Ext.mk₀ f)) h) = _
  rw [hf]
  apply (Ext.linearEquiv₀ :
    Ext (stageObj I M n) (stageObj I N m) 0 ≃ₗ[A]
      (stageObj I M n ⟶ stageObj I N m)).injective
  simp only [LinearEquiv.apply_symm_apply, hg]

end Factorisation

/-- Ext restriction factors through the prescribed pair of adic stages. -/
@[stacks 0G3L "existence of an adic Ext factorization at one stage"]
def FactorsAt
    (I : Ideal A) (M N : ModuleCat.{v} A) (p n m : ℕ) : Prop :=
  Nonempty (Factorisation I M N p n m)

/-- Existence of a single-stage factorization, written as an explicit lift and equation. -/
@[stacks 0G3L "single-stage adic Ext factorization criterion"]
theorem factorsAt_iff_exists
    (I : Ideal A) (M N : ModuleCat.{v} A) (p n m : ℕ) :
    FactorsAt I M N p n m ↔
      ∃ φ : Ext M N p →ₗ[A] Ext (stageObj I M n) (stageObj I N m) p,
        (subtypeExtPostcomp I (stageObj I M n) N m p).comp φ =
          subtypeExtPrecomp I M N n p := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.lift, D.fac⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨⟨φ, hφ⟩⟩

/-- A fixed cutoff gives adic Ext factorizations at every later stage. -/
@[stacks 0G3L "eventual adic Ext factorization"]
def EventuallyFactors
    (I : Ideal A) (M N : ModuleCat.{v} A) (p c : ℕ) : Prop :=
  ∀ n, c ≤ n → FactorsAt I M N p n (n - c)

/-- The explicit degree-zero factor works at every stage with cutoff zero. -/
@[stacks 0G3L "eventual degree-zero adic Ext factorization"]
theorem eventuallyFactors_zero (I : Ideal A) (M N : ModuleCat.{v} A) :
    EventuallyFactors I M N 0 0 := by
  intro n hn
  simpa using (show FactorsAt I M N 0 n n from
    ⟨Factorisation.degreeZero I M N (Nat.le_refl n)⟩)

/-- For a finite source over a Noetherian ring, one cutoff works in degree `q + 1` for every
target module. -/
@[stacks 0G3L "uniform positive-degree adic Ext factorization"]
theorem existsEventuallyFactors_succ
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{v} A) [Module.Finite A M] (q : ℕ) :
    ∃ c : ℕ, ∀ N : ModuleCat.{v} A, EventuallyFactors I M N (q + 1) c := sorry

/-- For a finite source over a Noetherian ring, one cutoff works in every fixed Ext degree and
for every target module. -/
@[stacks 0G3L "uniform all-degree adic Ext factorization"]
theorem existsEventuallyFactors
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{v} A) [Module.Finite A M] (p : ℕ) :
    ∃ c : ℕ, ∀ N : ModuleCat.{v} A, EventuallyFactors I M N p c := by
  by_cases hp : p = 0
  · subst p
    exact ⟨0, fun N ↦ eventuallyFactors_zero I M N⟩
  · obtain ⟨c, hc⟩ := existsEventuallyFactors_succ I M (p - 1)
    have hp' : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
    have hpeq : p - 1 + 1 = p := Nat.sub_add_cancel hp'
    refine ⟨c, ?_⟩
    intro N
    simpa [hpeq] using hc N

/-- Lemma 15.102.2 (0G3L): in positive degree, Ext restriction from a finite module over a
Noetherian ring eventually factors through the shifted adic stage of the target. -/
@[stacks 0G3L "Lemma 15.102.2"]
theorem existsFactorisation_of_pos
    [IsNoetherianRing A] (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M]
    (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, ∀ n ≥ c,
      ∃ φ : Ext M N p →ₗ[A] Ext (stageObj I M n) (stageObj I N (n - c)) p,
        ∀ x : Ext M N p,
          subtypeExtPostcomp I (stageObj I M n) N (n - c) p (φ x) =
            subtypeExtPrecomp I M N n p x := by
  obtain ⟨c, hc⟩ := existsEventuallyFactors_succ I M (p - 1)
  have hp' : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp)
  have hpeq : p - 1 + 1 = p := Nat.sub_add_cancel hp'
  refine ⟨c, ?_⟩
  intro n hn
  have hF : FactorsAt I M N p n (n - c) := by
    simpa [hpeq] using hc N n hn
  rcases hF with ⟨D⟩
  exact ⟨D.lift, fun x ↦ Factorisation.fac_apply D x⟩

end CategoryTheory.DerivedCategory.IdealPower.ExtRestriction
