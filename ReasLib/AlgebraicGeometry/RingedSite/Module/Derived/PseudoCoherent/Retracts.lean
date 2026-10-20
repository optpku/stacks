/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Triangulated
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Retracts of pseudo-coherent derived module sheaves

This leaf owns retract stability for fixed-degree and unbounded pseudo-coherence.  Biproduct
statements are exposed as the standard direct-summand consequences.
-/

open CategoryTheory CategoryTheory.Limits
open RingedSite.Hom (ModuleDerived)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The object property of being pseudo-coherent on a ringed site. -/
abbrev pseudoCoherent : ObjectProperty (ModuleDerived.{w} X) :=
  fun K => K.IsPseudoCoherent

/-- Fixed-degree pseudo-coherence is stable under retracts. -/
@[stacks 08FW "fixed-degree retract stability"]
instance mPseudoCoherent_isStableUnderRetracts (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts (mPseudoCoherent (X := X) m) := sorry

/-- Pseudo-coherence is stable under retracts. -/
@[stacks 08FW "retract stability"]
instance pseudoCoherent_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (pseudoCoherent (X := X)) := sorry

namespace IsMPseudoCoherent

/-- Lemma 21.45.6 (1,2): both summands of an `m`-pseudo-coherent biproduct are
`m`-pseudo-coherent. -/
@[stacks 08FW "(1,2)"]
theorem summands (K L : ModuleDerived.{w} X) [HasBinaryBiproduct K L] {m : ℤ}
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m ∧ L.IsMPseudoCoherent m := sorry

/-- Lemma 21.45.6 (1): the left summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 08FW "(1)"]
theorem left (K L : ModuleDerived.{w} X) [HasBinaryBiproduct K L] {m : ℤ}
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry

/-- Lemma 21.45.6 (2): the right summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 08FW "(2)"]
theorem right (K L : ModuleDerived.{w} X) [HasBinaryBiproduct K L] {m : ℤ}
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m := sorry

end IsMPseudoCoherent

namespace IsPseudoCoherent

/-- Lemma 21.45.6 (3,4): both summands of a pseudo-coherent biproduct are pseudo-coherent. -/
@[stacks 08FW "(3,4)"]
theorem summands (K L : ModuleDerived.{w} X) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent ∧ L.IsPseudoCoherent := sorry

/-- Lemma 21.45.6 (3): the left summand of a pseudo-coherent biproduct is pseudo-coherent. -/
@[stacks 08FW "(3)"]
theorem left (K L : ModuleDerived.{w} X) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry

/-- Lemma 21.45.6 (4): the right summand of a pseudo-coherent biproduct is pseudo-coherent. -/
@[stacks 08FW "(4)"]
theorem right (K L : ModuleDerived.{w} X) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    L.IsPseudoCoherent := sorry

end IsPseudoCoherent

end RingedSite.Hom.ModuleDerived
