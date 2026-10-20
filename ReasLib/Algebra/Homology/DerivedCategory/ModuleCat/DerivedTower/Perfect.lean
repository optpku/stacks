/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Characterization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect Limits of Derived Module Towers

This is the reusable owner for Stacks Project Tag 0CQG.  It shares the tower, limit, and
base-change infrastructure with the pseudo-coherent theorem while keeping the property-specific
perfectness argument separate.
@stack 0CQG
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedTower.Perfect

variable {A : SequentialInverseSystem CommRingCat.{u}}

/-- The all-stages-or-nilpotent-tail hypothesis for perfectness implies its pseudo-coherent
counterpart. -/
theorem allOrTail_isPseudoCoherent (T : DerivedTower A)
    (h_perfect : A.AllOrTail (fun n ↦ (T.obj n).IsPerfect)) :
    A.AllOrTail (fun n ↦ (T.obj n).IsPseudoCoherent) := sorry

/-- Lemma 15.98.3 (0CQG): a homotopy limit of a Cartesian derived module tower is perfect under
the stated surjectivity, local nilpotence, and stagewise perfectness alternative. -/
@[stacks 0CQG "(1), perfect inverse limit"]
theorem limit (T : DerivedTower A) (L : LimitCone A)
    (h_surjective : A.Surjective)
    (h_locallyNilpotent : A.KernelLocallyNilpotent)
    (h_perfect : A.AllOrTail (fun n ↦ (T.obj n).IsPerfect))
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict L.cone) K) :
    K.IsPerfect := sorry

namespace Limit

/-- Lemma 15.98.3 (0CQG): every canonical base-change map from a presented perfect limit to a
stage is an isomorphism. -/
@[stacks 0CQG "(2), perfect inverse-limit base change"]
theorem baseChangeMap_isIso (T : DerivedTower A) (L : LimitCone A)
    (h_surjective : A.Surjective)
    (h_locallyNilpotent : A.KernelLocallyNilpotent)
    (h_perfect : A.AllOrTail (fun n ↦ (T.obj n).IsPerfect))
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (P : HomotopyLimit.Presentation (T.restrict L.cone) K) (n : ℕ)
    (E : DerivedExtension (L.cone.stageMap n).hom) :
    IsIso (DerivedTower.Limit.BaseChange.map T L.cone P n E) := sorry

/-- Without choosing a homotopy-limit presentation publicly, derived base change of an intrinsic
perfect limit object is nonemptily isomorphic to every stage. -/
@[stacks 0CQG "presentation-independent perfect base change"]
theorem nonemptyIso (T : DerivedTower A) (L : LimitCone A)
    (h_surjective : A.Surjective)
    (h_locallyNilpotent : A.KernelLocallyNilpotent)
    (h_perfect : A.AllOrTail (fun n ↦ (T.obj n).IsPerfect))
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (L.cone.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict L.cone) K) (n : ℕ)
    (E : DerivedExtension (L.cone.stageMap n).hom) :
    Nonempty (DerivedTower.Limit.BaseChange.obj L.cone K n E ≅ T.obj n) := sorry

end Limit

end CategoryTheory.ModuleCat.DerivedTower.Perfect
