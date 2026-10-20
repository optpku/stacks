module

public import ReasLib.CategoryTheory.Abelian.Extension.Classification
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A A' B B' : C}
variable (a : A ⟶ A') (b : B' ⟶ B)

/- Lemma 12.6.3 [010L] (1): Baer sum makes extension classes an
additive commutative group. -/
@[stacks 010L]
#check (inferInstance : AddCommGroup (ExtensionClass A B))

/- Lemma 12.6.3 [010L] (2): pullback is additive in the right endpoint. -/
@[stacks 010L]
#check (ExtensionClass.pullbackAddHom b :
  ExtensionClass A B →+ ExtensionClass A B')

/- Lemma 12.6.3 [010L] (3): pushout is additive in the left endpoint. -/
@[stacks 010L]
#check (ExtensionClass.pushoutAddHom a :
  ExtensionClass A B →+ ExtensionClass A' B)

/- Lemma 12.6.3 [010L] (4): the canonical forward comparison is additive. -/
@[stacks 010L]
#check (ExtensionClass.toExtAddHom (A := A) (B := B) :
  ExtensionClass A B →+ Ext B A 1)

/- Lemma 12.6.3 [010L] (5): this additive comparison is bijective. -/
@[stacks 010L]
#check (ExtensionClass.toExt_bijective (A := A) (B := B) :
  Function.Bijective (ExtensionClass.toExt : ExtensionClass A B → Ext B A 1))

end CategoryTheory
