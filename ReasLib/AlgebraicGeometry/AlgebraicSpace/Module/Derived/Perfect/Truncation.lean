/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Order.Filter.AtTopBot.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.CategoryTheory.DerivedCategory.Ext

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a perfect derived module on a quasi-compact absolutely quasi-separated algebraic space,
eventual vanishing of morphisms out of negative shifts into a derived quasicoherent object is
equivalent to eventual vanishing after any lower truncation of the target. -/
theorem homSubsingletonEventually_iff_truncGE {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (E : DerivedQCoh X) (a : ℤ) :
    (∀ᶠ i : ℤ in Filter.atTop, Subsingleton (P⟦-i⟧ ⟶ E.obj)) ↔
      ∀ᶠ i : ℤ in Filter.atTop,
        Subsingleton (P⟦-i⟧ ⟶ (t.truncGE a).obj E.obj) := sorry

/-- For a perfect derived module on a quasi-compact absolutely quasi-separated algebraic space,
eventual vanishing of Ext into a derived quasicoherent object is equivalent to eventual vanishing
after any lower truncation of the target. -/
theorem extSubsingletonEventually_iff_truncGE {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (E : DerivedQCoh X) (a : ℤ) :
    (∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
      ∀ᶠ i : ℤ in Filter.atTop,
        Subsingleton (Ext⁽i⁾(P, (t.truncGE a).obj E.obj)) := sorry

/-- For a perfect derived module on a quasi-compact absolutely quasi-separated algebraic space,
vanishing of Ext into a derived quasicoherent object in sufficiently negative degrees is equivalent
to the same vanishing after any upper truncation of the target. -/
theorem extSubsingletonEventually_iff_truncLE {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (E : DerivedQCoh X) (a : ℤ) :
    (∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
        Subsingleton (Ext⁽i⁾(P, (t.truncLE a).obj E.obj)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
