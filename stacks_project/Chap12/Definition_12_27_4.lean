module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]
variable (X : C)
variable [EnoughInjectives C]

/-!
# Definition 12.27.4

Compatibility facade for mathlib's canonical enough-injectives interface.
-/

/- Definition 12.27.4 [0138]: every object admits a monomorphism into an injective object. -/
@[stacks 0138]
#check (CategoryTheory.EnoughInjectives C : Prop)

#check (fun X : C => CategoryTheory.EnoughInjectives.presentation X :
  ∀ X : C, Nonempty (CategoryTheory.InjectivePresentation X))
#check (CategoryTheory.InjectivePresentation X : Type (max u v))
