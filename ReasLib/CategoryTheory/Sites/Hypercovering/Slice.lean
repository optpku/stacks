/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal

/-!
# Slice hypercovering conversion

A hypercovering of an object `X` gives a hypercovering of the terminal presheaf
on the slice site `J.over X`, with the original simplicial family.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)

/-- The degree-`0` local-surjectivity condition for a hypercovering of `X`, viewed
on the slice site `J.over X`. -/
theorem zero_locallySurjective_slice :
    HypercoveringOf.Terminal.ZeroLocallySurjective (J.over X) K.toSimplicialObject := sorry

/-- The degree-`1` local-surjectivity condition for a hypercovering of `X`, viewed
on the slice site `J.over X`. -/
theorem one_locallySurjective_slice :
    HypercoveringOf.Terminal.OneLocallySurjective (J.over X) K.toSimplicialObject := sorry

/-- The higher matching-map local-surjectivity conditions for a hypercovering of
`X`, viewed on the slice site `J.over X`. -/
theorem higher_locallySurjective_slice :
    ∀ n : ℕ,
      HypercoveringOf.Terminal.HigherLocallySurjective (J.over X) K.toSimplicialObject
        (n + 1) := sorry

/-- The site-level hypercovering of the terminal presheaf on `C / X` associated to a
hypercovering of an object `X`. -/
@[reducible] def toSliceTerminal : HypercoveringOf.Terminal.{w} (J.over X) where
  simplicial := K.toSimplicialObject
  augmentation := HypercoveringOf.terminalAugmentation K.toSimplicialObject
  isLocalHypercover :=
    SimplicialObject.Augmented.IsLocalHypercover.of_zero_one_higher
      (zero_locallySurjective_slice J X K) (one_locallySurjective_slice J X K)
      (higher_locallySurjective_slice J X K)

/-- The underlying simplicial object of `toSliceTerminal` is the simplicial object of
the original hypercovering of `X`. -/
theorem toSliceTerminal_simplicial :
    (toSliceTerminal J X K).simplicial = K.toSimplicialObject := sorry

end CategoryTheory.Hypercovering
