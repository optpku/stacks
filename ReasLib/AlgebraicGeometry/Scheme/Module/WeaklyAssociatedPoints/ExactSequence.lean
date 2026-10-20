/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ExactSequence

/-!
# Weakly associated points in exact sequences

This module relates the weakly associated points of the terms in a short exact complex of
modules on a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- In a short exact complex of modules on a scheme, every weakly associated point of the
middle term belongs to the weakly-associated-point set of one of the outer terms. -/
theorem weakAss_middle_subset_union_of_shortExact
    (hS : S.ShortExact) :
    S.X₂.weakAss ⊆ S.X₁.weakAss ∪ S.X₃.weakAss := sorry

/-- In a short exact complex of modules on a scheme, every weakly associated point of the
left term is a weakly associated point of the middle term. -/
theorem weakAss_left_subset_of_shortExact
    (hS : S.ShortExact) :
    S.X₁.weakAss ⊆ S.X₂.weakAss := sorry

end AlgebraicGeometry.Scheme.Modules
