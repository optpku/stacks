/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Products
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Preservation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent tensoring and derived sequential limits

This leaf keeps the derived-limit statement independent of a chosen `R lim` notation and of a
chosen product cone.  Its public surface is the presentation-independent proposition
`HomotopyLimit.IsOf`; explicit Milnor presentations remain available through the compatibility
API when a consumer genuinely needs them.
@stack 0D2L
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.HomotopyLimit.IsOf

variable {R : Type u} [CommRing R]

/-- Stacks 0D2L: fixed-left derived tensoring by a pseudo-coherent module complex carries a
homotopy limit of a degree-zero module tower to a homotopy limit of the tensorized tower. -/
@[stacks 0D2L "pseudo-coherent tensor preserves a derived module limit"]
theorem tensor_single_of_isPseudoCoherent
    {K : DerivedCategory (ModuleCat.{u} R)}
    {M : SequentialInverseSystem (ModuleCat.{u} R)}
    {L : DerivedCategory (ModuleCat.{u} R)}
    (hL : HomotopyLimit.IsOf (M ⋙ ModuleCat.single0Functor) L)
    (hK : K.IsPseudoCoherent) :
    HomotopyLimit.IsOf
      ((M ⋙ ModuleCat.single0Functor) ⋙
        DerivedCategory.DerivedTensor.Bifunctor.leftFunctor K)
      ((DerivedCategory.DerivedTensor.Bifunctor.leftFunctor K).obj L) := sorry

end CategoryTheory.HomotopyLimit.IsOf
