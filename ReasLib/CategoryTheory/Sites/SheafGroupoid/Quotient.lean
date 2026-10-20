module

public import ReasLib.CategoryTheory.Sites.SheafGroupoid
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification

/-!
# Quotient stacks of internal sheaf groupoids

The quotient is the groupoid stackification of the co-Grothendieck category
of the section-valued groupoid presheaf.
-/

@[expose] public section

noncomputable section

universe u v a

namespace CategoryTheory.SheafGroupoid

open Limits Pseudofunctor.CoGrothendieck
open Functor.IsFibered.InGroupoids.Stackification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {B : Sheaf J (Type a)} [HasPullbacks (Sheaf J (Type a))]

/-- The prestack of an internal sheaf groupoid is the co-Grothendieck category
of its section groupoids, with its canonical groupoid-fibred projection. -/
def prestack (G : SheafGroupoid J B) : FiberedCategoryOver.Groupoids C :=
  FiberedCategoryOver.Groupoids.ofFunctor (groupoidPresheafProjection G.points)

/-- The prestack projection is the projection of the section groupoid presheaf. -/
theorem prestack_p (G : SheafGroupoid J B) :
    G.prestack.p = groupoidPresheafProjection G.points := rfl

/-- The concrete groupoid stackification presentation of the section prestack. -/
def quotientStackPresentation (G : SheafGroupoid J B) :
    Presentation J (groupoidPresheafProjection G.points) :=
  presentation J (groupoidPresheafProjection G.points)

/-- The quotient stack of an internal sheaf groupoid is the stackification
of its section prestack. -/
def quotientStack (G : SheafGroupoid J B) : StackOver.Groupoids J :=
  G.quotientStackPresentation.target

/-- The quotient stack is the target of its concrete stackification presentation. -/
theorem quotientStack_target (G : SheafGroupoid J B) :
    G.quotientStack = G.quotientStackPresentation.target := rfl

/-- The comparison from the section prestack to the quotient is a stackification. -/
theorem quotientStack_isStackification (G : SheafGroupoid J B) :
    CartesianBasedFunctor.IsStackification J G.quotientStackPresentation.comparison :=
  G.quotientStackPresentation.isStackification

end CategoryTheory.SheafGroupoid
