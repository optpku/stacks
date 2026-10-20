/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.DualNumber.Periodic.Projective
import StacksCheckRecall

/-!
# A module with a one-sided periodic projective resolution

This file recalls Example 15.69.3 from the reusable periodic dual-number resolution API. The
`ℕ`-indexed chain complex models the source's cohomological complex supported in nonpositive
degrees.

@stack 0A5Q
-/

@[expose] public section

universe u

-- The source module `M = k[ε] / (ε)`.
@[stacks 0A5Q "dual-number residue module"]
#check @DualNumber.residueModule

-- The concrete complex `⋯ → k[ε] → k[ε] → k[ε]`, with all maps multiplication by `ε`.
@[stacks 0A5Q "periodic projective complex"]
#check @DualNumber.Periodic.complex

@[stacks 0A5Q "periodic augmentation"]
#check @DualNumber.Periodic.augmentation

-- Example 15.69.3 (1): the augmentation is a quasi-isomorphism and all its terms are projective.
@[stacks 0A5Q "Example 15.69.3 (1)"]
#check fun (k : Type u) [Field k] ↦
  (inferInstance : QuasiIso (DualNumber.Periodic.augmentation k))

@[stacks 0A5Q "projective terms"]
#check @DualNumber.Periodic.termProjective

-- Example 15.69.3 (2): the residue module nevertheless has infinite projective dimension.
@[stacks 0A5Q "Example 15.69.3 (2)"]
#check @DualNumber.Periodic.residueModule_projectiveDimension_eq_top
