/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Limit.BaseChange

@[expose] public section

/-!
# Pseudo-coherent limits of derived module towers

This file is the reusable owner for the two conclusions of Stacks Project Tag 0CQF.  Intrinsic
pseudo-coherence uses `HomotopyLimit.IsOf`; a concrete base-change morphism is exposed only from
an explicit `HomotopyLimit.Presentation`.
@stack 0CQF
-/

open CategoryTheory
open CategoryTheory.Limits
open Filter

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedTower

variable {A : SequentialInverseSystem CommRingCat.{u}}

namespace PseudoCoherent

/-- Pseudo-coherence holds eventually in a Cartesian tower under the all-stages-or-nilpotent-tail
hypothesis. -/
theorem eventually (T : DerivedTower A) (h_surj : A.Surjective)
    (h_pc : A.AllOrTail (fun n ↦ (T.obj n).IsPseudoCoherent))
    (h_cart : T.IsCartesian) :
    ∀ᶠ n in atTop, (T.obj n).IsPseudoCoherent := sorry

/-- An intrinsic homotopy limit of an eventually pseudo-coherent Cartesian tower is
pseudo-coherent. -/
theorem of_eventually (T : DerivedTower A) (L : LimitCone A)
    (h_surj : A.Surjective) (h_locnil : A.KernelLocallyNilpotent)
    (h_cart : T.IsCartesian)
    (h_pc : ∀ᶠ n in atTop, (T.obj n).IsPseudoCoherent)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict L.cone) K) :
    K.IsPseudoCoherent := sorry

/-- Lemma 15.98.1 (1) (0CQF): a homotopy limit of a Cartesian derived module tower is
pseudo-coherent under the stated nilpotence and stagewise pseudo-coherence alternative. -/
@[stacks 0CQF "(1), pseudo-coherent inverse limit"]
theorem limit (T : DerivedTower A) (L : LimitCone A)
    (h_surj : A.Surjective) (h_locnil : A.KernelLocallyNilpotent)
    (h_pc : A.AllOrTail (fun n ↦ (T.obj n).IsPseudoCoherent))
    (h_cart : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict L.cone) K) :
    K.IsPseudoCoherent := sorry

namespace Limit

/-- The stage base-change comparison is an isomorphism when pseudo-coherence holds eventually. -/
theorem baseChangeMap_isIso_of_eventually (T : DerivedTower A) (L : LimitCone A)
    (h_surj : A.Surjective) (h_locnil : A.KernelLocallyNilpotent)
    (h_cart : T.IsCartesian)
    (h_pc : ∀ᶠ n in atTop, (T.obj n).IsPseudoCoherent)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (P : HomotopyLimit.Presentation (T.restrict L.cone) K) (n : ℕ)
    (E : DerivedExtension (L.cone.stageMap n).hom) :
    IsIso (DerivedTower.Limit.BaseChange.map T L.cone P n E) := sorry

/-- Lemma 15.98.1 (2) (0CQF): every stage base-change comparison of a presented homotopy limit
is an isomorphism. -/
@[stacks 0CQF "(2), derived base-change comparison"]
theorem baseChangeMap_isIso (T : DerivedTower A) (L : LimitCone A)
    (h_surj : A.Surjective) (h_locnil : A.KernelLocallyNilpotent)
    (h_pc : A.AllOrTail (fun n ↦ (T.obj n).IsPseudoCoherent))
    (h_cart : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (P : HomotopyLimit.Presentation (T.restrict L.cone) K) (n : ℕ)
    (E : DerivedExtension (L.cone.stageMap n).hom) :
    IsIso (DerivedTower.Limit.BaseChange.map T L.cone P n E) := sorry

/-- Without choosing a homotopy-limit presentation publicly, derived base change of an intrinsic
limit object is nonemptily isomorphic to every stage. -/
@[stacks 0CQF "presentation-independent derived base change"]
theorem nonemptyIso (T : DerivedTower A) (L : LimitCone A)
    (h_surj : A.Surjective) (h_locnil : A.KernelLocallyNilpotent)
    (h_pc : A.AllOrTail (fun n ↦ (T.obj n).IsPseudoCoherent))
    (h_cart : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict L.cone) K) (n : ℕ)
    (E : DerivedExtension (L.cone.stageMap n).hom) :
    Nonempty (DerivedTower.Limit.BaseChange.obj L.cone K n E ≅ T.obj n) := sorry

end Limit

end PseudoCoherent

end CategoryTheory.ModuleCat.DerivedTower
