module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Composition
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic

/-!
# Composition of setoid fibrations

Closure of the intrinsic projection-level owner under composition.
-/

@[expose] public section

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor.IsFibered.InSetoids.Comp

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/-- The composite of two functors fibred in setoids is fibred in setoids. -/
instance inSetoids
    (F : A ⥤ B) (G : B ⥤ C)
    [Functor.IsFibered.InSetoids F] [Functor.IsFibered.InSetoids G] :
    Functor.IsFibered.InSetoids (F ⋙ G) := sorry

end CategoryTheory.Functor.IsFibered.InSetoids.Comp
