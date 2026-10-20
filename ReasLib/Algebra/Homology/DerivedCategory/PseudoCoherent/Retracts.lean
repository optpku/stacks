/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Retracts of pseudo-coherent derived objects

This leaf owns the direct-summand closure of the absolute pseudo-coherence predicates.  The
biproduct consequences are deliberately exposed as small corollaries, so later developments can
use the retract instance without importing a chapter proof.

@stack 064X
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [Ring R]

/-- Lemma 15.65.8 (1): `m`-pseudo-coherence is stable under retracts in `D(R)`. -/
@[stacks 064X "m-pseudo-coherence is stable under retracts"]
instance isMPseudoCoherent_isStableUnderRetracts (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DerivedCategory (ModuleCat R) ↦ K.IsMPseudoCoherent m) := sorry

/-- Lemma 15.65.8 (2): pseudo-coherence is stable under retracts in `D(R)`. -/
@[stacks 064X "pseudo-coherence is stable under retracts"]
instance isPseudoCoherent_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (IsPseudoCoherent : ObjectProperty (DerivedCategory (ModuleCat R))) := sorry

/-- Lemma 15.65.8 (1): the left summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 064X "(1), left biproduct summand"]
theorem isMPseudoCoherent_left_of_biprod
    (K L : DerivedCategory (ModuleCat R)) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_left
    (fun X : DerivedCategory (ModuleCat R) ↦ X.IsMPseudoCoherent m) hKL

/-- Lemma 15.65.8 (2): the right summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 064X "(2), right biproduct summand"]
theorem isMPseudoCoherent_right_of_biprod
    (K L : DerivedCategory (ModuleCat R)) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_right
    (fun X : DerivedCategory (ModuleCat R) ↦ X.IsMPseudoCoherent m) hKL

/-- Lemma 15.65.8 (3): the left summand of a pseudo-coherent biproduct is pseudo-coherent. -/
@[stacks 064X "(3), left biproduct summand"]
theorem isPseudoCoherent_left_of_biprod
    (K L : DerivedCategory (ModuleCat R))
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_left
    (fun X : DerivedCategory (ModuleCat R) ↦ X.IsPseudoCoherent) hKL

/-- Lemma 15.65.8 (4): the right summand of a pseudo-coherent biproduct is pseudo-coherent. -/
@[stacks 064X "(4), right biproduct summand"]
theorem isPseudoCoherent_right_of_biprod
    (K L : DerivedCategory (ModuleCat R))
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    L.IsPseudoCoherent :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_right
    (fun X : DerivedCategory (ModuleCat R) ↦ X.IsPseudoCoherent) hKL

end CategoryTheory.DerivedCategory

end
