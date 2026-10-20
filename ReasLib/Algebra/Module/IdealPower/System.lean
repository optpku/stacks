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
      Ideal.map (Ideal.Quotient.mk (I ^ (n : ℕ))) (I ^ c) := sorry

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
        (⊤ : Submodule (stageRing A I n) M) = ⊥ := sorry

/-- The stage-ideal torsion predicate is equivalent to the canonical torsion submodule being all
of the module.  This is the bridge used by quotient and annihilator APIs. -/
@[stacks 0EGW "stage-ideal torsion as a full torsion submodule"]
theorem isTorsionByStageIdealPower_iff_torsionBySet_eq_top
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ+) (c : ℕ)
    (M : Type v) [AddCommGroup M] [Module (stageRing A I n) M] :
    Module.IsTorsionBySet (stageRing A I n) M
        (↑(stageIdeal A I n ^ c) : Set (stageRing A I n)) ↔
      Submodule.torsionBySet (stageRing A I n) M
        (↑(stageIdeal A I n ^ c) : Set (stageRing A I n)) = ⊤ := sorry

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
    powerSubmodule d X n ≤ powerSubmodule c X n := sorry

/-- The canonical inclusion between nested ideal-power submodules. -/
@[stacks 0EGW "ideal-power submodule inclusion"]
abbrev powerSubmoduleInclusion (X : IadicFiniteModuleSystem A I)
    {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    powerSubmodule d X n →ₗ[stageRing A I n] powerSubmodule c X n :=
  Submodule.inclusion (powerSubmodule_le X h n)

/-- Monotonicity of torsion submodules. -/
@[stacks 0EGW "monotonicity of torsion submodules"]
theorem torsionSubmodule_le (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    torsionSubmodule c X n ≤ torsionSubmodule d X n := sorry

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
    restrictedLevelMap f d n x ∈ (quotientPowerMap f.cutoff d Y n.1).range := sorry

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
    (quotientPowerMap c g.cutoff Y n.1).ker ≤ (promotedAux c g n).ker := sorry

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
      promotedAux c g n y := sorry

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
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The congruence generated by one-step promotion. -/
@[stacks 0EGW "promotion congruence on representatives"]
def relation (A : Type u) [CommRing A] (I : Ideal A) :
    HomRel (IadicFiniteModuleSystem A I) :=
  fun _ _ f g ↦ Relation.EqvGen promotesTo f g

/-- Promotion is compatible with representative composition. -/
@[stacks 0EGW "promotion congruence compatibility"]
instance relationCongruence (A : Type u) [CommRing A] (I : Ideal A) :
    Congruence (relation A I) :=
  { equivalence := sorry
    comp_left := sorry
    comp_right := sorry }

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
    ((quotient A I).obj X).as = X := sorry

/-- Two representatives define the same quotient-category morphism exactly when they are related
by the promotion congruence. -/
@[stacks 0EGW "equality of quotient morphisms represented by promotion"]
theorem quotient_map_eq_iff {X Y : IadicFiniteModuleSystem A I}
    (f g : HomRepresentative X Y) :
    (quotient A I).map f = (quotient A I).map g ↔
      HomRepresentative.relation A I f g := sorry

end Category

end IadicFiniteModuleSystem
