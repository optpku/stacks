module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Category.Monomorphism

@[expose] public section

universe u v

open CategoryTheory

/- Lemma 87.26.2: a composite of monomorphisms of formal algebraic spaces is a
monomorphism (such monomorphisms being categorical `Mono` as in 87.26.1,
specializing to injective maps of the relevant sheaves). -/
@[stacks 0GHT] #check (CategoryTheory.Mono.comp :
  ∀ {C : Type u} [Category.{v} C] {X Y Z : C}
    (first : X ⟶ Y) (second : Y ⟶ Z) [Mono first] [Mono second],
    Mono (first ≫ second))
