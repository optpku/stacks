/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.CategoryTheory.Generator.Subobject
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Extension from Subobjects of a Test Object

For objects `U` and `I`, the predicate `Generator.HasSubobjectExtension U I` says that every map
from a subobject of `U` to `I` extends across the subobject inclusion.  The definition and its
basic injectivity implication are independent of zero objects and Grothendieck hypotheses.
-/

open CategoryTheory

universe v u

namespace CategoryTheory.Generator

variable {C : Type u} [Category.{v} C]

/-- Every map from a subobject of `U` to `I` extends to a map from `U`. -/
@[stacks 079G "generator subobject extension property"]
def HasSubobjectExtension (U I : C) : Prop :=
  ∀ (M : Subobject U) (φ : (M : C) ⟶ I),
    ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ

namespace HasSubobjectExtension

/-- Injectivity implies extension from subobjects of every test object. -/
theorem of_injective {U I : C} (hI : Injective I) :
    HasSubobjectExtension U I := sorry

end HasSubobjectExtension

end CategoryTheory.Generator
