/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import ReasLib.CategoryTheory.Generator.SubobjectExtension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Subobject Extension as a Lifting Property

This file identifies extension from subobjects of a test object with the right lifting property
against Mathlib's `generatingMonomorphisms` family.  It is separated from the underlying predicate
so users of the elementary extension API need not import Grothendieck-category infrastructure.
-/

open CategoryTheory Limits ZeroObject
open CategoryTheory.IsGrothendieckAbelian
open CategoryTheory.MorphismProperty

universe v u

namespace CategoryTheory.Generator.HasSubobjectExtension

variable {C : Type u} [Category.{v} C]

/-- Extension from subobjects of `U` is the right lifting property against the corresponding
generating monomorphisms, for any morphism from `I` to a zero object. -/
@[stacks 079G "subobject extension as a lifting property"]
theorem iff_rlp_of_isZero [HasZeroMorphisms C] {U I Z : C}
    (p : I ⟶ Z) (hZ : IsZero Z) :
    Generator.HasSubobjectExtension U I ↔ (generatingMonomorphisms U).rlp p := sorry

/-- Extension from subobjects of `U` is the right lifting property against its generating
monomorphisms for the canonical map from `I` to zero. -/
theorem iff_rlp_zero [HasZeroMorphisms C] [HasZeroObject C] {U I : C} :
    Generator.HasSubobjectExtension U I ↔
      (generatingMonomorphisms U).rlp (0 : I ⟶ 0) := sorry

end CategoryTheory.Generator.HasSubobjectExtension
