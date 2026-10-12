/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Generator.SubobjectExtension.Lifting
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Injectivity Tested on Subobjects of a Generator

In a Grothendieck abelian category, extension from subobjects of one separator detects injective
objects.  The intermediate lifting-property statement is exposed separately for downstream use.
-/

open CategoryTheory Limits ZeroObject
open CategoryTheory.IsGrothendieckAbelian
open CategoryTheory.MorphismProperty

universe w v u

namespace CategoryTheory.Generator.HasSubobjectExtension

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {U I : C}

/-- For a separator in a Grothendieck abelian category, subobject extension is equivalent to the
right lifting property against all monomorphisms. -/
theorem iff_rlp_monomorphisms_zero (hU : IsSeparator U) :
    Generator.HasSubobjectExtension U I ↔
      (monomorphisms C).rlp (0 : I ⟶ 0) := sorry

/-- Extension from all subobjects of a separator implies injectivity. -/
theorem to_injective (h : Generator.HasSubobjectExtension U I) (hU : IsSeparator U) :
    Injective I := sorry

/-- Lemma 19.11.6: an object is injective exactly when maps from subobjects of a separator extend
to the separator. -/
@[stacks 079G "injectivity tested on generator subobjects"]
theorem injective_iff (hU : IsSeparator U) :
    Injective I ↔ Generator.HasSubobjectExtension U I := sorry

end CategoryTheory.Generator.HasSubobjectExtension
