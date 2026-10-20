module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.CrossRefAttribute

/-!
# Over-identity equations for based natural transformations

This module gives the bridge between based natural transformations and the textbook global
over-identity equation for their underlying natural transformations.
-/

@[expose] public section

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Functor.IsHomLift
open scoped Bicategory

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

namespace BasedNatTrans

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {F G : X ⥤ᵇ Y}

/-- The textbook over-identity equation recovered from the canonical based natural
transformation. -/
theorem over_id (η : F ⟶ G) :
    eqToHom F.w.symm ≫ Functor.whiskerRight η.toNatTrans Y.p ≫ eqToHom G.w = 𝟙 X.p := sorry
/- Proof strategy: apply `IsHomLift.fac` to every component of `η`, reverse the resulting
component equation, and use extensionality for natural transformations. The transports by `F.w`
and `G.w` are exactly the two `eqToHom` factors in the statement. -/

/-- The component of a natural transformation satisfying the global over-identity equation is a
hom lift of the corresponding identity in the base. -/
theorem ofOverId.isHomLift (τ : F.toFunctor ⟶ G.toFunctor)
    (overId : eqToHom F.w.symm ≫ Functor.whiskerRight τ Y.p ≫ eqToHom G.w = 𝟙 X.p)
    (a : X.obj) : Y.p.IsHomLift (𝟙 (X.p.obj a)) (τ.app a) := sorry
/- Proof strategy: evaluate `overId` at `a`, reverse the component equality, and apply
`IsHomLift.of_fac` using the objectwise projection equalities `F.w_obj a` and `G.w_obj a`. -/

/-- Build a based natural transformation from the textbook over-identity equation. -/
def ofOverId (τ : F.toFunctor ⟶ G.toFunctor)
    (overId : eqToHom F.w.symm ≫ Functor.whiskerRight τ Y.p ≫ eqToHom G.w = 𝟙 X.p) :
    F ⟶ G where
  toNatTrans := τ
  isHomLift' := ofOverId.isHomLift τ overId

end BasedNatTrans

end CategoryTheory

/- Definition 4.33.9 (Stacks 02XP): the canonical mathlib owner for vertical `2`-morphisms
between based functors. -/
