module

public import ReasLib.CategoryTheory.Filtration.Object
public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import ReasLib.CategoryTheory.Subobject.Quotient

/-!
# Complete Filtrations

A decreasing filtration is complete if the ambient object is the inverse limit of its
quotient system `A / F^p A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

namespace DecreasingFiltration

variable {A : C}

/-- The quotient object `A / F^p A`. -/
abbrev quotientObj (F : DecreasingFiltration A) (p : ℤ) : C :=
  cokernel (F.stage p).arrow

/-- The quotient system functor `ℤᵒᵖ ⥤ C` sends `p` to `A / F^p A`. -/
def quotientSystem (F : DecreasingFiltration A) : ℤᵒᵖ ⥤ C where
  obj p := F.quotientObj (unop p)
  map f := subobjectQuotientMap (F.antitone (leOfHom f.unop))
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The canonical cone from A to the quotient system. -/
def quotientSystemCone (F : DecreasingFiltration A) : Cone (F.quotientSystem) where
  pt := A
  π :=
    { app := fun p => cokernel.π (F.stage (unop p)).arrow
      naturality := sorry }

/-- A decreasing filtration is complete if the canonical cone to its quotient system is a limit. -/
def IsComplete (F : DecreasingFiltration A) : Prop :=
  Nonempty (IsLimit (F.quotientSystemCone))

/-- A decreasing filtration that reaches the zero subobject at one stage is complete. -/
theorem isComplete_of_stage_eq_bot [HasZeroObject C] (F : DecreasingFiltration A)
    {b : ℤ} (hbot : F.stage b = ⊥) :
    IsComplete F := sorry

/-- A finite decreasing filtration is complete: a zero stage makes its quotient tower eventually
constant at the ambient object. -/
theorem isComplete_of_isFinite [HasZeroObject C] (F : DecreasingFiltration A)
    (hfinite : IndexedFiltration.IsFinite F) :
    IsComplete F := sorry

end DecreasingFiltration

end CategoryTheory
