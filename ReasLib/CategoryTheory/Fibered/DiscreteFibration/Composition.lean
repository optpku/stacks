module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Basic

/-!
# Composition of discrete fibrations

Discrete fibrations are closed under composition.  This is the canonical typeclass owner used by
composite projections, including universe-resizing presentations.
-/

@[expose] public section

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/-- A composite of discrete fibrations is a discrete fibration. -/
instance IsDiscreteFibration.comp
    (F : A ⥤ B) (G : B ⥤ C)
    [F.IsDiscreteFibration] [G.IsDiscreteFibration] :
    (F ⋙ G).IsDiscreteFibration := sorry

end CategoryTheory.Functor
