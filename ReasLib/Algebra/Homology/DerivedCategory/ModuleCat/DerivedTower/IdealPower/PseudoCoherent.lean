/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Limit
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.PseudoCoherent
import ReasLib.Algebra.Category.CommRingCat.IdealPower.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-Coherent Limits of Ideal-Power Towers

This file specializes the generic pseudo-coherent derived-tower API to the canonical positive
ideal-power system.  It owns pseudo-coherence of the limit and invertibility of the concrete
base-change map; derived completeness lives in the property-independent `Completeness` leaf.

@stack 09AV
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTower.PseudoCoherent

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Lemma 15.98.2 (09AV), pseudo-coherence clause: the homotopy limit of a Cartesian
ideal-power tower with pseudo-coherent first stage is pseudo-coherent. -/
@[stacks 09AV "(1), pseudo-coherent ideal-power limit"]
theorem limit [IsAdicComplete I A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsPseudoCoherent)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : HomotopyLimit.IsOf T.toBase K) :
    K.IsPseudoCoherent := sorry

namespace Limit

/-- Lemma 15.98.2 (09AV), base-change clause: the map from the presented limit after base change
to stage `n` is an isomorphism in every explicit derived extension model. -/
@[stacks 09AV "(3), pseudo-coherent ideal-power limit base change"]
theorem baseChangeMap_isIso [IsAdicComplete I A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsPseudoCoherent)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (P : HomotopyLimit.Presentation T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    IsIso (IdealPowerTower.Limit.baseChangeMap T P n E) := sorry

/-- Without choosing a homotopy-limit presentation publicly, base change of the intrinsic
pseudo-coherent limit is nonemptily isomorphic to stage `n`. -/
@[stacks 09AV "presentation-independent pseudo-coherent ideal-power base change"]
theorem nonemptyIso [IsAdicComplete I A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsPseudoCoherent)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : HomotopyLimit.IsOf T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    Nonempty (IdealPowerTower.Limit.baseChange K n E ≅ T.obj n) := sorry

end Limit

end CategoryTheory.ModuleCat.IdealPowerTower.PseudoCoherent
