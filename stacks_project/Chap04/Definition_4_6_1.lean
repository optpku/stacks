module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import StacksCheckRecall

@[expose] public section


namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {P X Y S : C} (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
variable (h : IsPullback p q f g)

/- Mathlib's `IsPullback p q f g` is the source-facing owner: unlike the lower-level
`IsLimit (PullbackCone.mk p q h)`, it packages the commutativity witness, and unlike
`Square.IsPullback`, it does not first bundle the diagram as a `Square`. This choice makes no
generalization—the source's fibre-product object, `p`, and `q` are the implicit `P`, `fst`, and
`snd`—and exposes `exists_lift` and `hom_ext` directly for downstream universal-property
arguments. -/

/- Definition 4.6.1: saying that morphisms `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as the fibre
product of `f : X ⟶ S` and `g : Y ⟶ S` is exactly the canonical pullback-square predicate
`IsPullback p q f g`. -/
@[stacks 001V "fibre product by a commutative pullback square and universal property"]
#check (IsPullback p q f g : Prop)

/- Companion recall: the commuting-square clause is the canonical projection
`IsPullback.toCommSq`. -/
#check h.toCommSq

/- Companion recall: the existence clause in the textbook universal property is the canonical
theorem `IsPullback.exists_lift`. -/
#check h.exists_lift

/- Companion recall: the uniqueness clause in the textbook universal property is the canonical
theorem `IsPullback.hom_ext`. -/
#check h.hom_ext

/- Companion recall: the converse direction from a limiting pullback cone is the canonical
constructor `IsPullback.of_isLimit`. -/
#check IsPullback.of_isLimit

end CategoryTheory
