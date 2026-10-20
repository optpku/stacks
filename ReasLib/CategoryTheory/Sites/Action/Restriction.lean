/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import ReasLib.CategoryTheory.Sites.Action.JointlySurjective
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Restriction between jointly-surjective action sites

The reusable site-theoretic facts for restriction of actions along a monoid homomorphism live
here, independently of any later sheaf or point calculation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Action

/-- Restriction of actions along `φ` preserves finite limits. -/
theorem res_preservesFiniteLimits {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H) :
    PreservesFiniteLimits (Action.res (Type u) φ) := sorry

/-- Restriction of actions along `φ` is representably flat. -/
instance res_representablyFlat {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H) :
    RepresentablyFlat (Action.res (Type u) φ) := sorry

/-- Restriction of actions along `φ` preserves jointly-surjective covering families. -/
theorem res_coverPreserving {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H) :
    CoverPreserving (jointlySurjectiveTopology H) (jointlySurjectiveTopology G)
      (Action.res (Type u) φ) := sorry

/-- Restriction of actions along `φ` is continuous for the jointly-surjective topologies. -/
@[instance 10000]
instance res_isContinuous {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H) :
    (Action.res (Type u) φ).IsContinuous (jointlySurjectiveTopology H)
      (jointlySurjectiveTopology G) := sorry

/-- If `φ` is injective, restriction along `φ` is cover-dense for the jointly-surjective
topology. This is the categorical form of presenting every `G`-action as a quotient of a
restricted `H`-action. -/
theorem res_isCoverDense_of_injective {G H : Type u} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) :
    (Action.res (Type u) φ).IsCoverDense (jointlySurjectiveTopology G) := sorry

end Action
