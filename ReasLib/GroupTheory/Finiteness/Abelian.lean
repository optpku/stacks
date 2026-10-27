/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: Basic.lean:147-151, SelmerGroup.lean:98-166.
Changes: relocated general group infrastructure to its mathematical owner;
declaration names, hypotheses, and proof bodies are preserved.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import ReasLib.GroupTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Int.Basic

/-!
# Finitely generated commutative groups and power quotients

Finite generation of a commutative group agrees with finite generation of its
additive form as a `ℤ`-module. Noetherianity then gives finite generation of
subgroups. A finitely generated commutative group of nonzero finite exponent is
finite, so its quotient by `n`-th powers is finite for `n ≠ 0`.

The quotient is Mathlib's `QuotientGroup` by the range of `powMonoidHom`; no
second carrier is defined. Applications include finite-index subgroups, finite
abelian quotients, unit power classes, and arithmetic descent. These results
require no ring, Dedekind domain, fraction field, or number field as input.
-/

@[expose] public section

/-- A commutative group is finitely generated iff it is finitely generated as a `ℤ`-module. -/
theorem Module.finite_int_additive (G : Type*) [CommGroup G] [Group.FG G] :
    Module.Finite ℤ (Additive G) :=
  Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr ‹_›)

/-- A commutative group that is finitely generated as a `ℤ`-module is finitely generated as a
group; converse direction of `Module.finite_int_additive`. -/
theorem Group.fg_of_module_finite_int {G : Type*} [CommGroup G]
    (h : Module.Finite ℤ (Additive G)) : Group.FG G :=
  AddGroup.fg_iff_mul_fg.mp (Module.Finite.iff_addGroup_fg.mp h)

/-- A subgroup of a finitely generated commutative group is finitely generated, as `ℤ` is a
Noetherian ring. (The proof passes through `Additive G`, so `to_additive` cannot translate it;
an additive version would have to be stated by hand.) -/
theorem Subgroup.fg_of_commGroup_fg {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G) :
    Group.FG H :=
  have : Module.Finite ℤ (Additive G) := Module.finite_int_additive G
  Group.fg_of_module_finite_int <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)

/-- A finitely generated commutative group of finite exponent is finite. -/
theorem CommGroup.finite_of_fg_of_pow_eq_one {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ)
    [NeZero n] (hn : ∀ x : G, x ^ n = 1) : Finite G := by
  let _ : Module (ZMod n) (Additive G) := AddCommGroup.zmodModule (n := n) hn
  have h₁ : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (by rwa [AddGroup.fg_iff_mul_fg])
  have h₂ : Module.Finite (ZMod n) (Additive G) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod n) (Additive G)
  have := Module.finite_of_finite (ZMod n) (M := Additive G)
  exact Finite.of_equiv _ (Additive.toMul (α := G))

/-- The group of `n`-th power classes of a finitely generated commutative group is finite. -/
theorem CommGroup.finite_modPow {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ) [NeZero n] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  have : Group.FG (G ⧸ (powMonoidHom n : G →* G).range) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  refine finite_of_fg_of_pow_eq_one n fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H g => exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

end
