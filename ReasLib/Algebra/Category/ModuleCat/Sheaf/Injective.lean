module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective sheaves of modules

This file records the injectivity behavior of the canonical inclusion of module sheaves into
module presheaves on an arbitrary site.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- Forgetting a sheaf of modules to its underlying presheaf of modules preserves injective
objects. -/
@[stacks 03FB "functorial form"]
instance forgetPreservesInjectiveObjects (R : Sheaf J RingCat.{w}) :
    (forget.{z} R).PreservesInjectiveObjects := sorry

/-! The section-level consequence belongs next to the injectivity bridge rather than to a
particular geometric site. -/

/-- Surjective restriction of sections of an injective module sheaf along a monomorphism. -/
@[stacks 093X "injective module restriction is surjective"]
theorem restriction_surjective_of_injective
    {R : Sheaf J RingCat.{w}} {U U' : C} (a : U' ⟶ U) [Mono a]
    (ℐ : SheafOfModules.{z} R) (hℐ : Injective ℐ) :
    Function.Surjective (((forget.{z} R).obj ℐ).map a.op) := sorry

-- This is a Prop-valued preservation instance; its deferred proof is the only `sorryAx` debt.

end SheafOfModules
