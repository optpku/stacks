/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.Ext
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A A' B B' : C}
variable (S T : Extension A B) (a : A ⟶ A') (b : B' ⟶ B)

/- Definition 12.6.2 [010K]: extension classes use Mathlib's canonical
isomorphism setoid on the category of fixed-endpoint extensions. -/
@[stacks 010K]
#check (ExtensionClass A B : Type _)

#check (isIsomorphicSetoid (Extension A B) : Setoid (Extension A B))
#check (Extension.isomorphic_iff_isIsomorphic (S := S) (T := T) :
  Extension.Isomorphic S T ↔ IsIsomorphic S T)
#check (Extension.pullback b S : Extension A B')
#check (Extension.pushout a S : Extension A' B)
#check (Extension.baerSum S T : Extension A B)
#check (ExtensionClass.pullback b : ExtensionClass A B → ExtensionClass A B')
#check (ExtensionClass.pushout a : ExtensionClass A B → ExtensionClass A' B)
#check (ExtensionClass.toExt :
  ExtensionClass A B → Ext B A 1)

end CategoryTheory
