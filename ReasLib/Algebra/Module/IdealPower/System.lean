/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite modules in an ideal-power system

This file owns the representative presentation and quotient category for finite
A / I ^ n-module systems.  Chapter files only expose the public API.

@stack 0EGW
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace IadicFiniteModuleSystem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The quotient ring at a positive stage. -/
@[stacks 0EGW "stage ring of a finite ideal-power system"]
abbrev stageRing (n : ℕ+) := A ⧸ I ^ (n : ℕ)

end IadicFiniteModuleSystem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Remark 15.101.6 (1): a positive-indexed system of finite modules over the corresponding
quotient rings. -/
@[stacks 0EGW "Remark 15.101.6 (1)"]
abbrev IadicFiniteModuleSystem :=
  ∀ n : ℕ+, FGModuleCat.{v} (IadicFiniteModuleSystem.stageRing A I n)

namespace IadicFiniteModuleSystem

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The image of the ground ideal in the stage ring. -/
@[stacks 0EGW "stage ideal in the quotient ring"]
abbrev stageIdeal (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ+) :
    Ideal (stageRing A I n) :=
  Ideal.map (Ideal.Quotient.mk (I ^ (n : ℕ))) I

/-- Powers of the stage ideal are images of the corresponding powers of the ground ideal. -/
@[stacks 0EGW "powers of the stage ideal"]
theorem stageIdeal_pow_eq_map (A : Type u) [CommRing A] (I : Ideal A)
    (n : ℕ+) (c : ℕ) :
    stageIdeal A I n ^ c =
      Ideal.map (Ideal.Quotient.mk (I ^ (n : ℕ))) (I ^ c) := by
  simpa [stageIdeal] using
    (Ideal.map_pow (Ideal.Quotient.mk (I ^ (n : ℕ))) I c).symm

/-- The cth ideal-power submodule of a stage. -/
@[stacks 0EGW "ideal-power submodule of a stage"]
abbrev powerSubmodule (c : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    Submodule (stageRing A I n) (X n) :=
  (stageIdeal A I n) ^ c • ⊤

/-- The submodule killed by the cth power of the stage ideal. -/
@[stacks 0EGW "ideal-power torsion submodule of a stage"]
abbrev torsionSubmodule (c : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    Submodule (stageRing A I n) (X n) :=
  Submodule.torsionBySet (stageRing A I n) (X n) ↑(stageIdeal A I n ^ c)

/-- The quotient of a stage by its c-torsion submodule. -/
@[stacks 0EGW "torsion quotient of a stage"]
abbrev torsionQuotient (c : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :=
  X n ⧸ torsionSubmodule c X n

/-- Being killed by the cth stage-ideal power is equivalent to vanishing of its action on the
whole module. -/
@[stacks 0EGW "stage-ideal torsion as vanishing of the power action"]
theorem isTorsionByStageIdealPower_iff
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ+) (c : ℕ)
    (M : Type v) [AddCommGroup M] [Module (stageRing A I n) M] :
    Module.IsTorsionBySet (stageRing A I n) M
        (↑(stageIdeal A I n ^ c) : Set (stageRing A I n)) ↔
      stageIdeal A I n ^ c •
        (⊤ : Submodule (stageRing A I n) M) = ⊥ := by
  constructor
  · intro h
    apply le_bot_iff.mp
    exact Submodule.smul_le.mpr fun a ha x _ ↦ @h x ⟨a, ha⟩
  · intro h x a
    have hx : (a : stageRing A I n) • x ∈
        stageIdeal A I n ^ c • (⊤ : Submodule (stageRing A I n) M) :=
      Submodule.smul_mem_smul a.2 (by trivial)
    rw [h] at hx
    exact hx

/-- The stage-ideal torsion predicate is equivalent to the canonical torsion submodule being all
of the module.  This is the bridge used by quotient and annihilator APIs. -/
@[stacks 0EGW "stage-ideal torsion as a full torsion submodule"]
theorem isTorsionByStageIdealPower_iff_torsionBySet_eq_top
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ+) (c : ℕ)
    (M : Type v) [AddCommGroup M] [Module (stageRing A I n) M] :
    Module.IsTorsionBySet (stageRing A I n) M
        (↑(stageIdeal A I n ^ c) : Set (stageRing A I n)) ↔
      Submodule.torsionBySet (stageRing A I n) M
        (↑(stageIdeal A I n ^ c) : Set (stageRing A I n)) = ⊤ := by
  exact Module.isTorsionBySet_iff_torsionBySet_eq_top _

/-- Remark 15.101.6 (2): a representative of a morphism, defined from a cutoff onward. -/
@[stacks 0EGW "Remark 15.101.6 (2)"]
structure HomRepresentative (X Y : IadicFiniteModuleSystem A I) where
  /-- The cutoff from which the family is defined. -/
  cutoff : ℕ
  /-- The stagewise maps on the ideal-power source and torsion quotient target. -/
  map (n : ℕ+) (_ : cutoff ≤ (n : ℕ)) :
    powerSubmodule cutoff X n →ₗ[stageRing A I n] torsionQuotient cutoff Y n

namespace HomRepresentative

variable {X Y Z W : IadicFiniteModuleSystem A I}

/-- Coercion from a representative to its admissible family of stage maps. -/
@[stacks 0EGW "representative evaluation coercion"]
instance : CoeFun (HomRepresentative X Y) (fun f ↦
    ∀ n : ℕ+, f.cutoff ≤ (n : ℕ) →
      powerSubmodule f.cutoff X n →ₗ[stageRing A I n] torsionQuotient f.cutoff Y n) where
  coe f := f.map

/-- A positive level together with a cutoff inequality. -/
@[stacks 0EGW "admissible level for a representative"]
abbrev AdmissibleLevel (c : ℕ) := {n : ℕ+ // c ≤ (n : ℕ)}

/-- The quotient map from a deeper ideal-power submodule to a torsion quotient. -/
@[stacks 0EGW "ideal-power quotient map"]
abbrev quotientPowerMap (c d : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    powerSubmodule d X n →ₗ[stageRing A I n] torsionQuotient c X n :=
  (torsionSubmodule c X n).mkQ.comp (powerSubmodule d X n).subtype

/-- Monotonicity of ideal-power submodules. -/
@[stacks 0EGW "monotonicity of ideal-power submodules"]
theorem powerSubmodule_le (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    powerSubmodule d X n ≤ powerSubmodule c X n := by
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

/-- The canonical inclusion between nested ideal-power submodules. -/
@[stacks 0EGW "ideal-power submodule inclusion"]
abbrev powerSubmoduleInclusion (X : IadicFiniteModuleSystem A I)
    {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    powerSubmodule d X n →ₗ[stageRing A I n] powerSubmodule c X n :=
  Submodule.inclusion (powerSubmodule_le X h n)

/-- Monotonicity of torsion submodules. -/
@[stacks 0EGW "monotonicity of torsion submodules"]
theorem torsionSubmodule_le (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    torsionSubmodule c X n ≤ torsionSubmodule d X n := by
  exact Submodule.torsionBySet_le_torsionBySet_pow c d h (stageIdeal A I n)

/-- The quotient transition induced by enlarging the torsion cutoff. -/
@[stacks 0EGW "torsion quotient transition"]
noncomputable abbrev torsionQuotientMap (X : IadicFiniteModuleSystem A I)
    {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    torsionQuotient c X n →ₗ[stageRing A I n] torsionQuotient d X n :=
  (torsionSubmodule c X n).mapQ
    (torsionSubmodule d X n) LinearMap.id (torsionSubmodule_le X h n)

/-- Promotion raises a representative cutoff by one and transports source and target. -/
@[stacks 0EGW "one-step promotion of a representative"]
noncomputable def successor (f : HomRepresentative X Y) : HomRepresentative X Y where
  cutoff := f.cutoff + 1
  map n hn :=
    (torsionQuotientMap Y (Nat.le_succ f.cutoff) n).comp
      ((f n (Nat.le_trans (Nat.le_succ f.cutoff) hn)).comp
        (powerSubmoduleInclusion X (Nat.le_succ f.cutoff) n))

/-- A representative restricted to a deeper source power. -/
@[stacks 0EGW "restricted representative map"]
noncomputable abbrev restrictedLevelMap (f : HomRepresentative X Y) (d : ℕ)
    (n : AdmissibleLevel (f.cutoff + d)) :
    powerSubmodule (f.cutoff + d) X n.1 →ₗ[stageRing A I n.1] torsionQuotient f.cutoff Y n.1 :=
  (f n.1 (Nat.le_trans (Nat.le_add_right f.cutoff d) n.2)).comp
    (powerSubmoduleInclusion X (Nat.le_add_right f.cutoff d) n.1)

/-- The restricted image lies in the quotient-power range needed for composition. -/
@[stacks 0EGW "representative image in quotient-power range"]
theorem image_mem_range (f : HomRepresentative X Y) (d : ℕ)
    (n : AdmissibleLevel (f.cutoff + d))
    (x : powerSubmodule (f.cutoff + d) X n.1) :
    restrictedLevelMap f d n x ∈ (quotientPowerMap f.cutoff d Y n.1).range := by
  let F := f n.1 (Nat.le_trans (Nat.le_add_right f.cutoff d) n.2)
  have hx : (x : X n.1) ∈
      stageIdeal A I n.1 ^ d • powerSubmodule f.cutoff X n.1 := by
    simpa only [powerSubmodule, Nat.add_comm f.cutoff d, pow_add, mul_smul] using x.2
  have hincl : stageIdeal A I n.1 ^ d • powerSubmodule f.cutoff X n.1 ≤
      powerSubmodule f.cutoff X n.1 := Submodule.smul_le_right
  have hmem : ∀ y (hy : y ∈ stageIdeal A I n.1 ^ d • powerSubmodule f.cutoff X n.1),
      F ⟨y, hincl hy⟩ ∈ (quotientPowerMap f.cutoff d Y n.1).range := by
    intro y hy
    refine Submodule.smul_induction_on' hy ?_ ?_
    · intro r hr y hy
      obtain ⟨z, hz⟩ := (torsionSubmodule f.cutoff Y n.1).mkQ_surjective (F ⟨y, hy⟩)
      refine LinearMap.mem_range.mpr ⟨⟨r • z, Submodule.smul_mem_smul hr (by trivial)⟩, ?_⟩
      change (torsionSubmodule f.cutoff Y n.1).mkQ (r • z) = F (r • ⟨y, hy⟩)
      rw [map_smul, map_smul, hz]
    · intro y hy z hz ihy ihz
      change F (⟨y, hincl hy⟩ + ⟨z, hincl hz⟩) ∈
        (quotientPowerMap f.cutoff d Y n.1).range
      rw [map_add]
      exact Submodule.add_mem _ ihy ihz
  exact hmem x.1 hx

/-- The restricted representative, bundled as a map into its quotient-power range. -/
@[stacks 0EGW "representative map into quotient-power range"]
noncomputable def toRange (f : HomRepresentative X Y) (d : ℕ)
    (n : AdmissibleLevel (f.cutoff + d)) :
    powerSubmodule (f.cutoff + d) X n.1 →ₗ[stageRing A I n.1]
      (quotientPowerMap f.cutoff d Y n.1).range :=
  LinearMap.codRestrict _ (restrictedLevelMap f d n) (image_mem_range f d n)

/-- The promoted target map before descending through the quotient-power range. -/
@[stacks 0EGW "promoted target map before descent"]
noncomputable def promotedAux (c : ℕ) (g : HomRepresentative Y Z)
    (n : AdmissibleLevel (c + g.cutoff)) :
    powerSubmodule g.cutoff Y n.1 →ₗ[stageRing A I n.1]
      torsionQuotient (c + g.cutoff) Z n.1 :=
  (torsionQuotientMap Z (Nat.le_add_left g.cutoff c) n.1).comp
    (g n.1 (Nat.le_trans (Nat.le_add_left g.cutoff c) n.2))

/-- The quotient-power kernel is killed by the promoted target map. -/
@[stacks 0EGW "kernel descent for promoted target map"]
theorem quotientPowerMap_ker_le_promotedAux_ker (c : ℕ)
    (g : HomRepresentative Y Z) (n : AdmissibleLevel (c + g.cutoff)) :
    (quotientPowerMap c g.cutoff Y n.1).ker ≤ (promotedAux c g n).ker := by
  intro x hx
  let G := g n.1 (Nat.le_trans (Nat.le_add_left g.cutoff c) n.2)
  have hxT : (x : Y n.1) ∈ torsionSubmodule c Y n.1 := by
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨z, hz⟩ := (torsionSubmodule g.cutoff Z n.1).mkQ_surjective (G x)
  have hzT : stageIdeal A I n.1 ^ (c + g.cutoff) ≤
      Ideal.torsionOf (stageRing A I n.1) (Z n.1) z := by
    rw [pow_add]
    refine Ideal.mul_le.mpr ?_
    intro r hr s hs
    have hrx : r • x = 0 :=
      Subtype.ext ((Submodule.mem_torsionBySet_iff _ _).mp hxT ⟨r, hr⟩)
    have hrz : r • z ∈ torsionSubmodule g.cutoff Z n.1 := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (torsionSubmodule g.cutoff Z n.1).mkQ (r • z) = 0
      rw [map_smul, hz, ← map_smul, hrx, map_zero]
    change (r * s) • z = 0
    rw [mul_comm, mul_smul]
    exact (Submodule.mem_torsionBySet_iff _ _).mp hrz ⟨s, hs⟩
  change torsionQuotientMap Z (Nat.le_add_left g.cutoff c) n.1 (G x) = 0
  rw [← hz]
  change (torsionSubmodule (c + g.cutoff) Z n.1).mkQ z = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (Submodule.mem_torsionBySet_iff _ _).mpr fun r ↦ hzT r.2

/-- The quotient lift of the promoted target map before identifying its range. -/
@[stacks 0EGW "quotient lift of the promoted target map"]
noncomputable def promotedLift (c : ℕ) (g : HomRepresentative Y Z)
    (n : AdmissibleLevel (c + g.cutoff)) :
    (powerSubmodule g.cutoff Y n.1 ⧸
        (quotientPowerMap c g.cutoff Y n.1).ker) →ₗ[stageRing A I n.1]
      torsionQuotient (c + g.cutoff) Z n.1 :=
  (quotientPowerMap c g.cutoff Y n.1).ker.liftQ
    (promotedAux c g n)
    (quotientPowerMap_ker_le_promotedAux_ker c g n)

/-- The promoted target map descended to the quotient-power range. -/
@[stacks 0EGW "promoted target map on quotient-power range"]
noncomputable def promoted (c : ℕ) (g : HomRepresentative Y Z)
    (n : AdmissibleLevel (c + g.cutoff)) :
    (quotientPowerMap c g.cutoff Y n.1).range →ₗ[stageRing A I n.1]
      torsionQuotient (c + g.cutoff) Z n.1 :=
  (promotedLift c g n).comp
    (quotientPowerMap c g.cutoff Y n.1).quotKerEquivRange.symm.toLinearMap

/-- Evaluation of the descended promoted map on a canonical quotient-power witness. -/
@[simp, stacks 0EGW "evaluation of the promoted quotient-power map"]
theorem promoted_apply (c : ℕ) (g : HomRepresentative Y Z)
    (n : AdmissibleLevel (c + g.cutoff)) (y : powerSubmodule g.cutoff Y n.1) :
    promoted c g n ⟨quotientPowerMap c g.cutoff Y n.1 y, LinearMap.mem_range_self _ y⟩ =
      promotedAux c g n y := by
  change promotedLift c g n
    ((quotientPowerMap c g.cutoff Y n.1).quotKerEquivRange.symm _) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- Promotion relation on raw representatives. -/
@[stacks 0EGW "promotion relation on representatives"]
def promotesTo (f g : HomRepresentative X Y) : Prop := g = successor f

/-- The identity representative. -/
@[stacks 0EGW "identity representative"]
noncomputable def id (X : IadicFiniteModuleSystem A I) : HomRepresentative X X where
  cutoff := 0
  map n _ := quotientPowerMap 0 0 X n

/-- Composition of representatives, with additive cutoff. -/
@[stacks 0EGW "composition of representatives"]
noncomputable def comp (f : HomRepresentative X Y) (g : HomRepresentative Y Z) :
    HomRepresentative X Z where
  cutoff := f.cutoff + g.cutoff
  map n hn :=
    (promoted f.cutoff g ⟨n, hn⟩).comp (toRange f g.cutoff ⟨n, hn⟩)

/-- Compute composition using a witness in the intermediate ideal power. -/
theorem comp_apply_of_eq (f : HomRepresentative X Y) (g : HomRepresentative Y Z)
    (n : ℕ+) (hn : f.cutoff + g.cutoff ≤ (n : ℕ))
    (x : powerSubmodule (f.cutoff + g.cutoff) X n)
    (y : powerSubmodule g.cutoff Y n)
    (hy : quotientPowerMap f.cutoff g.cutoff Y n y =
      restrictedLevelMap f g.cutoff ⟨n, hn⟩ x) :
    comp f g n hn x = promotedAux f.cutoff g ⟨n, hn⟩ y := by
  have h : toRange f g.cutoff ⟨n, hn⟩ x =
      ⟨quotientPowerMap f.cutoff g.cutoff Y n y, LinearMap.mem_range_self _ y⟩ :=
    Subtype.ext hy.symm
  change promoted f.cutoff g ⟨n, hn⟩ (toRange f g.cutoff ⟨n, hn⟩ x) = _
  rw [h, promoted_apply]

/-- Compute composition from compatible quotient representatives. -/
theorem comp_apply_eq_mk (f : HomRepresentative X Y) (g : HomRepresentative Y Z)
    (n : ℕ+) (hn : f.cutoff + g.cutoff ≤ (n : ℕ))
    (x : powerSubmodule (f.cutoff + g.cutoff) X n)
    (y : powerSubmodule g.cutoff Y n) (z : Z n)
    (hf : restrictedLevelMap f g.cutoff ⟨n, hn⟩ x =
      (torsionSubmodule f.cutoff Y n).mkQ y)
    (hg : g n (Nat.le_trans (Nat.le_add_left g.cutoff f.cutoff) hn) y =
      (torsionSubmodule g.cutoff Z n).mkQ z) :
    comp f g n hn x = (torsionSubmodule (f.cutoff + g.cutoff) Z n).mkQ z := by
  rw [comp_apply_of_eq f g n hn x y hf.symm]
  change torsionQuotientMap Z (Nat.le_add_left g.cutoff f.cutoff) n (g n _ y) = _
  rw [hg]
  rfl

/-- Representatives are equal when their cutoffs and stage maps agree. -/
theorem ext_of_cutoff (f g : HomRepresentative X Y) (hc : f.cutoff = g.cutoff)
    (hmap : ∀ (n : ℕ+) (hf : f.cutoff ≤ (n : ℕ)) (hg : g.cutoff ≤ (n : ℕ))
      (x : X n) (hx : x ∈ powerSubmodule f.cutoff X n)
      (hx' : x ∈ powerSubmodule g.cutoff X n),
      HEq (f n hf ⟨x, hx⟩) (g n hg ⟨x, hx'⟩)) : f = g := by
  cases f with
  | mk c φ =>
    cases g with
    | mk d ψ =>
      dsimp at hc
      subst d
      congr 1
      funext n hn
      apply LinearMap.ext
      intro x
      exact eq_of_heq (hmap n hn hn x.1 x.2 x.2)

/-- Equality of cutoffs identifies the canonical quotient classes. -/
theorem torsion_mkQ_heq {c d : ℕ} (hc : c = d) (X : IadicFiniteModuleSystem A I)
    (n : ℕ+) (x : X n) :
    HEq ((torsionSubmodule c X n).mkQ x) ((torsionSubmodule d X n).mkQ x) := by
  cases hc
  rfl

/-- The identity representative is a left identity for composition. -/
theorem id_comp_eq (f : HomRepresentative X Y) : comp (id X) f = f := by
  apply ext_of_cutoff (comp (id X) f) f (Nat.zero_add f.cutoff)
  intro n hf hg x hx hx'
  obtain ⟨z, hz⟩ := (torsionSubmodule f.cutoff Y n).mkQ_surjective (f n hg ⟨x, hx'⟩)
  have h := comp_apply_eq_mk (id X) f n hf ⟨x, hx⟩ ⟨x, hx'⟩ z rfl hz.symm
  apply (heq_of_eq h).trans
  exact (torsion_mkQ_heq (Nat.zero_add f.cutoff) Y n z).trans (heq_of_eq hz)

/-- The identity representative is a right identity for composition. -/
theorem comp_id_eq (f : HomRepresentative X Y) : comp f (id Y) = f := by
  apply ext_of_cutoff (comp f (id Y)) f (Nat.add_zero f.cutoff)
  intro n hf hg x hx hx'
  obtain ⟨y, hy⟩ := (torsionSubmodule f.cutoff Y n).mkQ_surjective (f n hg ⟨x, hx'⟩)
  have hy0 : y ∈ powerSubmodule 0 Y n := by simp [powerSubmodule]
  have h := comp_apply_eq_mk f (id Y) n hf ⟨x, hx⟩ ⟨y, hy0⟩ y hy.symm rfl
  exact heq_of_eq (h.trans hy)

/-- Composition of representatives is associative before passing to promotion classes. -/
theorem comp_assoc_eq (f : HomRepresentative X Y) (g : HomRepresentative Y Z)
    (h : HomRepresentative Z W) : comp (comp f g) h = comp f (comp g h) := by
  apply ext_of_cutoff (comp (comp f g) h) (comp f (comp g h))
    (Nat.add_assoc f.cutoff g.cutoff h.cutoff)
  intro n hl hr x hxl hxr
  have hab : f.cutoff + g.cutoff ≤ (n : ℕ) :=
    (Nat.le_add_right (f.cutoff + g.cutoff) h.cutoff).trans hl
  have hbc : g.cutoff + h.cutoff ≤ (n : ℕ) :=
    (Nat.le_add_left (g.cutoff + h.cutoff) f.cutoff).trans hr
  have hc : h.cutoff ≤ (n : ℕ) := (Nat.le_add_left h.cutoff g.cutoff).trans hbc
  have hx : x ∈ powerSubmodule (f.cutoff + g.cutoff) X n :=
    powerSubmodule_le X (Nat.le_add_right (f.cutoff + g.cutoff) h.cutoff) n hxl
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp
    (image_mem_range f (g.cutoff + h.cutoff) ⟨n, hr⟩ ⟨x, hxr⟩)
  have hyb : (y : Y n) ∈ powerSubmodule g.cutoff Y n :=
    powerSubmodule_le Y (Nat.le_add_right g.cutoff h.cutoff) n y.2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (image_mem_range g h.cutoff ⟨n, hbc⟩ y)
  obtain ⟨t, ht⟩ := (torsionSubmodule h.cutoff W n).mkQ_surjective (h n hc z)
  have hfg := comp_apply_eq_mk f g n hab ⟨x, hx⟩ ⟨y.1, hyb⟩ z.1 hy.symm hz.symm
  have hleft := comp_apply_eq_mk (comp f g) h n hl ⟨x, hxl⟩ z t hfg ht.symm
  have hgh := comp_apply_eq_mk g h n hbc y z t hz.symm ht.symm
  have hright := comp_apply_eq_mk f (comp g h) n hr ⟨x, hxr⟩ y t hy.symm hgh
  exact (heq_of_eq hleft).trans
    ((torsion_mkQ_heq (Nat.add_assoc f.cutoff g.cutoff h.cutoff) W n t).trans
      (heq_of_eq hright.symm))

/-- Raising the target representative cutoff raises the composite cutoff. -/
theorem comp_successor_eq (f : HomRepresentative X Y) (g : HomRepresentative Y Z) :
    comp f (successor g) = successor (comp f g) := by
  apply ext_of_cutoff (comp f (successor g)) (successor (comp f g))
    (Nat.add_assoc f.cutoff g.cutoff 1).symm
  intro n hl hr x hxl hxr
  have hab : f.cutoff + g.cutoff ≤ (n : ℕ) :=
    (Nat.le_succ (f.cutoff + g.cutoff)).trans hr
  have hb : g.cutoff ≤ (n : ℕ) := (Nat.le_add_left g.cutoff f.cutoff).trans hab
  have hx : x ∈ powerSubmodule (f.cutoff + g.cutoff) X n :=
    powerSubmodule_le X (Nat.le_succ (f.cutoff + g.cutoff)) n hxr
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp
    (image_mem_range f (g.cutoff + 1) ⟨n, hl⟩ ⟨x, hxl⟩)
  let yb := powerSubmoduleInclusion Y (Nat.le_succ g.cutoff) n y
  obtain ⟨z, hz⟩ := (torsionSubmodule g.cutoff Z n).mkQ_surjective (g n hb yb)
  have hfg := comp_apply_eq_mk f g n hab ⟨x, hx⟩ yb z hy.symm hz.symm
  have hleft : comp f (successor g) n hl ⟨x, hxl⟩ =
      (torsionSubmodule (f.cutoff + (g.cutoff + 1)) Z n).mkQ z := by
    apply comp_apply_eq_mk f (successor g) n hl ⟨x, hxl⟩ y z hy.symm
    change torsionQuotientMap Z (Nat.le_succ g.cutoff) n (g n _ yb) = _
    rw [← hz]
    rfl
  have hright : successor (comp f g) n hr ⟨x, hxr⟩ =
      (torsionSubmodule (f.cutoff + g.cutoff + 1) Z n).mkQ z := by
    change torsionQuotientMap Z (Nat.le_succ (f.cutoff + g.cutoff)) n
      (comp f g n hab ⟨x, hx⟩) = _
    exact congrArg (torsionQuotientMap Z (Nat.le_succ (f.cutoff + g.cutoff)) n) hfg
  exact (heq_of_eq hleft).trans
    ((torsion_mkQ_heq (Nat.add_assoc f.cutoff g.cutoff 1).symm Z n z).trans
      (heq_of_eq hright.symm))

/-- Raising the source representative cutoff raises the composite cutoff. -/
theorem successor_comp_eq (f : HomRepresentative X Y) (g : HomRepresentative Y Z) :
    comp (successor f) g = successor (comp f g) := by
  apply ext_of_cutoff (comp (successor f) g) (successor (comp f g))
    (Nat.add_right_comm f.cutoff 1 g.cutoff)
  intro n hl hr x hxl hxr
  have hab : f.cutoff + g.cutoff ≤ (n : ℕ) :=
    (Nat.le_succ (f.cutoff + g.cutoff)).trans hr
  have hb : g.cutoff ≤ (n : ℕ) := (Nat.le_add_left g.cutoff f.cutoff).trans hab
  have hn : f.cutoff + (g.cutoff + 1) ≤ (n : ℕ) := by
    rw [← Nat.add_assoc]
    exact hr
  have hx : x ∈ powerSubmodule (f.cutoff + g.cutoff) X n :=
    powerSubmodule_le X (Nat.le_succ (f.cutoff + g.cutoff)) n hxr
  have hx' : x ∈ powerSubmodule (f.cutoff + (g.cutoff + 1)) X n := by
    rw [← Nat.add_assoc]
    exact hxr
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp
    (image_mem_range f (g.cutoff + 1) ⟨n, hn⟩ ⟨x, hx'⟩)
  let yb := powerSubmoduleInclusion Y (Nat.le_succ g.cutoff) n y
  obtain ⟨z, hz⟩ := (torsionSubmodule g.cutoff Z n).mkQ_surjective (g n hb yb)
  have hfg := comp_apply_eq_mk f g n hab ⟨x, hx⟩ yb z hy.symm hz.symm
  have hleft : comp (successor f) g n hl ⟨x, hxl⟩ =
      (torsionSubmodule (f.cutoff + 1 + g.cutoff) Z n).mkQ z := by
    apply comp_apply_eq_mk (successor f) g n hl ⟨x, hxl⟩ yb z _ hz.symm
    change torsionQuotientMap Y (Nat.le_succ f.cutoff) n
      (restrictedLevelMap f (g.cutoff + 1) ⟨n, hn⟩ ⟨x, hx'⟩) = _
    rw [← hy]
    rfl
  have hright : successor (comp f g) n hr ⟨x, hxr⟩ =
      (torsionSubmodule (f.cutoff + g.cutoff + 1) Z n).mkQ z := by
    change torsionQuotientMap Z (Nat.le_succ (f.cutoff + g.cutoff)) n
      (comp f g n hab ⟨x, hx⟩) = _
    exact congrArg (torsionQuotientMap Z (Nat.le_succ (f.cutoff + g.cutoff)) n) hfg
  exact (heq_of_eq hleft).trans
    ((torsion_mkQ_heq (Nat.add_right_comm f.cutoff 1 g.cutoff) Z n z).trans
      (heq_of_eq hright.symm))

/-- The equivalence relation generated by one-step promotion. -/
@[stacks 0EGW "promotion equivalence on representatives"]
instance : Setoid (HomRepresentative X Y) :=
  Relation.EqvGen.setoid promotesTo

/-- The representative category before quotienting by promotion. -/
@[stacks 0EGW "representative category of finite module systems"]
instance representativeCategory (A : Type u) [CommRing A] (I : Ideal A) :
    CategoryTheory.Category (IadicFiniteModuleSystem A I) where
  Hom X Y := HomRepresentative X Y
  id := id
  comp f g := comp f g
  id_comp := fun f ↦ id_comp_eq f
  comp_id := fun f ↦ comp_id_eq f
  assoc := fun f g h ↦ comp_assoc_eq f g h

/-- The congruence generated by one-step promotion. -/
@[stacks 0EGW "promotion congruence on representatives"]
def relation (A : Type u) [CommRing A] (I : Ideal A) :
    HomRel (IadicFiniteModuleSystem A I) :=
  fun _ _ f g ↦ Relation.EqvGen promotesTo f g

/-- Promotion is compatible with representative composition. -/
@[stacks 0EGW "promotion congruence compatibility"]
instance relationCongruence (A : Type u) [CommRing A] (I : Ideal A) :
    Congruence (relation A I) :=
  { equivalence := Relation.EqvGen.is_equivalence promotesTo
    comp_left := by
      intro X Y Z f g g' h
      change Relation.EqvGen promotesTo g g' at h
      induction h with
      | rel g g' h =>
        change g' = successor g at h
        subst g'
        exact Relation.EqvGen.rel _ _ (comp_successor_eq f g)
      | refl g => exact Relation.EqvGen.refl _
      | symm g g' h ih => exact Relation.EqvGen.symm _ _ ih
      | trans g g' g'' h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    comp_right := by
      intro X Y Z f f' g h
      change Relation.EqvGen promotesTo f f' at h
      induction h with
      | rel f f' h =>
        change f' = successor f at h
        subst f'
        exact Relation.EqvGen.rel _ _ (successor_comp_eq f g)
      | refl f => exact Relation.EqvGen.refl _
      | symm f f' h ih => exact Relation.EqvGen.symm _ _ ih
      | trans f f' f'' h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂ }

end HomRepresentative

/-- Remark 15.101.6 (2): the category obtained by quotienting morphism representatives by
promotion. -/
@[stacks 0EGW "Remark 15.101.6 (2)"]
abbrev Category (A : Type u) [CommRing A] (I : Ideal A) :=
  CategoryTheory.Quotient (HomRepresentative.relation A I)

namespace Category

/-- The canonical quotient functor from representatives. -/
@[stacks 0EGW "quotient functor for finite ideal-power systems"]
abbrev quotient (A : Type u) [CommRing A] (I : Ideal A) :
    IadicFiniteModuleSystem A I ⥤ IadicFiniteModuleSystem.Category A I :=
  CategoryTheory.Quotient.functor (HomRepresentative.relation A I)

/-- The quotient functor leaves system objects unchanged. -/
@[simp, stacks 0EGW "object formula for the quotient functor"]
theorem quotient_obj_as (X : IadicFiniteModuleSystem A I) :
    ((quotient A I).obj X).as = X := rfl

/-- Two representatives define the same quotient-category morphism exactly when they are related
by the promotion congruence. -/
@[stacks 0EGW "equality of quotient morphisms represented by promotion"]
theorem quotient_map_eq_iff {X Y : IadicFiniteModuleSystem A I}
    (f g : HomRepresentative X Y) :
    (quotient A I).map f = (quotient A I).map g ↔
      HomRepresentative.relation A I f g := by
  exact CategoryTheory.Quotient.functor_map_eq_iff
    (HomRepresentative.relation A I) f g

end Category

end IadicFiniteModuleSystem
