module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe v u u'

section

variable {C : Type u} [Category.{v} C]
variable {Ω : Type u'} (I : Ω → C) [HasProduct I] [∀ ω, Injective (I ω)]

/- Lemma 12.27.3: if `I : Ω → C` is a family of injective objects and the product `∏ᶜ I`
exists, then `∏ᶜ I` is injective. This is exactly the canonical product instance for
`Injective`. -/
@[stacks 0137] #check (inferInstance : Injective (∏ᶜ I))

end
