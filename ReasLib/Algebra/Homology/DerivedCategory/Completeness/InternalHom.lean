/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completion and derived internal Hom

Derived completion commutes with derived internal Hom in the target, and the completion unit in
the source induces an isomorphism into a derived-complete target.

@stack 0A6E
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped DerivedInternalHom

universe u

namespace DerivedCategory.DerivedCompletion

variable {A : Type u} [CommRing A]

-- Local declaration justification (source-local notation): abbreviate the fixed ambient derived
-- category while keeping the monoidal closed structure explicit as a parameter.
local notation "DMod" => DerivedCategory (ModuleCat A)

namespace InternalHom

/-- A derived internal Hom whose target is derived complete remains derived complete. -/
@[stacks 0A6E "derived-complete internal-Hom target"]
theorem target_isDerivedComplete
    (I : Ideal A) (hI : I.FG) [MonoidalCategory DMod] (H : MonoidalClosed DMod)
    (K L : DMod) :
    (RHom[H](K, derivedCompletionOf I hI L)).IsDerivedCompleteWithRespectTo I := sorry

/-- The canonical comparison from the completion of `RHom[H](K, L)` to
`RHom[H](K, L^∧)`, obtained from the universal property of derived completion. -/
@[stacks 0A6E "internal-Hom completion comparison map"]
noncomputable def comparison
    (I : Ideal A) (hI : I.FG) [MonoidalCategory DMod] (H : MonoidalClosed DMod)
    (K L : DMod) :
    derivedCompletionOf I hI (RHom[H](K, L)) ⟶
      RHom[H](K, derivedCompletionOf I hI L) :=
  DerivedCompletion.lift I hI (target_isDerivedComplete I hI H K L)
    (CategoryTheory.DerivedCategory.InternalHom.mapOf H (𝟙 K)
      (toDerivedCompletion I hI L))

/-- The comparison map is characterized by its composite with the completion unit. -/
@[stacks 0A6E "internal-Hom comparison unit equation"]
theorem toDerivedCompletion_comp_comparison
    (I : Ideal A) (hI : I.FG) [MonoidalCategory DMod] (H : MonoidalClosed DMod)
    (K L : DMod) :
    toDerivedCompletion I hI (RHom[H](K, L)) ≫ comparison I hI H K L =
      CategoryTheory.DerivedCategory.InternalHom.mapOf H (𝟙 K)
        (toDerivedCompletion I hI L) := sorry

/-- Lemma 15.92.13 (1): the canonical comparison from the derived completion of
`RHom[H](K, L)` to `RHom[H](K, L^∧)` is an isomorphism. -/
@[stacks 0A6E "(1), derived completion commutes with derived internal Hom in the target"]
theorem comparison_isIso
    (I : Ideal A) (hI : I.FG) [MonoidalCategory DMod] (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIso (comparison I hI H K L) := sorry

/-- The morphism on derived internal Hom induced by the completion unit in its source. -/
@[stacks 0A6E "internal-Hom source completion map"]
noncomputable abbrev unitMap
    (I : Ideal A) (hI : I.FG) [MonoidalCategory DMod] (H : MonoidalClosed DMod)
    (K L : DMod) :
    RHom[H](derivedCompletionOf I hI K, derivedCompletionOf I hI L) ⟶
      RHom[H](K, derivedCompletionOf I hI L) :=
  CategoryTheory.DerivedCategory.InternalHom.mapOf H
    (toDerivedCompletion I hI K) (𝟙 (derivedCompletionOf I hI L))

/-- Lemma 15.92.13 (2): the completion unit `K ⟶ K^∧` induces an isomorphism
`RHom[H](K^∧, L^∧) ⟶ RHom[H](K, L^∧)`. -/
@[stacks 0A6E "(2), derived internal Hom inverts the completion unit in its source"]
theorem unitMap_isIso
    (I : Ideal A) (hI : I.FG) [MonoidalCategory DMod] (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIso (unitMap I hI H K L) := sorry

end InternalHom

end DerivedCategory.DerivedCompletion
