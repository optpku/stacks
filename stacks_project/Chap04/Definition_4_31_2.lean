module

public import ReasLib.CategoryTheory.Bicategory.Biterminal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom
import StacksCheckRecall

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} (f : x ⟶ z) (g : y ⟶ z)
variable (P : Bicategory.PseudoPullbackCone f g)

section Source

variable [Bicategory.IsLocallyGroupoid B]

/- Definition 4.31.2: a `2`-fibre product square over `f : x ⟶ z` and `g : y ⟶ z` is the
biterminal object among `2`-commutative squares over this cospan. The locally groupoidal hypothesis
records the source assumption that the ambient bicategory is a `(2,1)`-category. -/
@[stacks 003Q "2-fibre product as a final 2-commutative square"]
#check (Bicategory.IsBiterminal P : Prop)

end Source

end CategoryTheory
