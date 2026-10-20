/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Perfect derived modules and open pushforward

This leaf records the closed-support criterion under which derived direct image along an open
immersion preserves perfectness. The public theorem depends only on perfectness and the intrinsic
degreewise support property.
-/

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}} {U : Opens X.carrier}

/-- Lemma 20.49.10: a perfect derived module on an open subspace remains perfect after derived
pushforward when all its cohomology is supported on a subset closed in the ambient space. -/
@[stacks 08DP]
theorem IsPerfect.pushforwardFromOpen_of_isSupportedOn
    {E : moduleDerivedOnOpen X U} (hE : IsPerfect E)
    {T : Set U} (hT : IsClosed (Subtype.val '' T)) (h_support : IsSupportedOn E T) :
    IsPerfect ((modulePushforwardFromOpenDerived U).obj E) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
