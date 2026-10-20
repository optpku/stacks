module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {P E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e]

/-!
# Definition 12.28.1

Compatibility facade for mathlib's canonical projective-object interface.
-/

/- Definition 12.28.1 [013B]: projectivity is the left lifting property against epimorphisms. -/
@[stacks 013B]
#check (CategoryTheory.Projective P : Prop)

section

variable [Projective P]

#check (CategoryTheory.Projective.factors f e : ∃ f' : P ⟶ E, f' ≫ e = f)
#check (CategoryTheory.Projective.factorThru f e : P ⟶ E)

end
