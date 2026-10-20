/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ExactSequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated points in exact sequences

This module relates the weakly associated points of the terms in a short exact complex of
quasi-coherent modules on an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {C : ShortComplex X.Modules}

/-- In a short exact complex of quasi-coherent modules on an algebraic space, every weakly
associated point of the middle term is weakly associated to one of the outer terms. -/
@[stacks 0CTZ]
theorem weakAss_middle_subset_union_of_shortExact_of_isQuasicoherent
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : C.ShortExact) :
    C.X₂.weakAss ⊆ C.X₁.weakAss ∪ C.X₃.weakAss :=
  sorry

/-- In a short exact complex of quasi-coherent modules on an algebraic space, every weakly
associated point of the left term is weakly associated to the middle term. -/
@[stacks 0CTZ]
theorem weakAss_left_subset_of_shortExact_of_isQuasicoherent
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : C.ShortExact) :
    C.X₁.weakAss ⊆ C.X₂.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
