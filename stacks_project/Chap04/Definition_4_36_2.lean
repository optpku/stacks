module

public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Strict
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable (p : S ⥤ C)

/- Definition 4.36.2: a split fibred category is intrinsically represented by
`Functor.IsFibered.Split`; its strict co-Grothendieck presentation is the canonical recognition
theorem below. -/
@[stacks 02XW]
#check (Functor.IsFibered.Split.iff_existsCoGrothendieckModel p :
  Functor.IsFibered.Split p ↔
    ∃ F : Cᵒᵖ ⥤ Cat.{v₂, u₂},
      Nonempty (BasedCategory.StrictIso (BasedCategory.ofFunctor p)
        (BasedCategory.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor'))))

end CategoryTheory
