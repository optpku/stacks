module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Cover

@[expose] public section

/-!
# Injective Object-Property Embeddings

This leaf exposes the object-property consequence of enough injectives. It is
independent of cochain complexes and of abelian structure, so resolution
constructions can use the same canonical instance without a local bridge.
-/

open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Stacks 013K: whenever a category has enough injectives, every object embeds
monomorphically into an injective object. -/
@[stacks 013K]
instance isInjective_hasMonoEmbedding [EnoughInjectives C] :
    HasMonoEmbedding (isInjective C) := sorry

end CategoryTheory
