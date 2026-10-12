/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {J X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f]

/-!
# Definition 12.27.1

Compatibility facade for mathlib's canonical injective-object interface.
-/

/- Definition 12.27.1 [0135]: injectivity is the right lifting property against monomorphisms. -/
@[stacks 0135]
#check (CategoryTheory.Injective J : Prop)

section

variable [Injective J]

#check (CategoryTheory.Injective.factors g f : ∃ h : Y ⟶ J, f ≫ h = g)
#check (CategoryTheory.Injective.factorThru g f : Y ⟶ J)

end
