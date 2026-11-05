module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Basic

@[expose] public section

/-!
# Structure on functors of bounded cochain complexes

The restricted bounded-above and bounded cochain functors inherit additive and
shift-compatible structure from the ambient termwise functor.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Cochain

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

namespace Minus

/-- The bounded-above cochain functor induced by an additive functor is additive. -/
instance additive (F : C ⥤ D) [F.Additive] : (map F).Additive := sorry

/-- The bounded-above cochain functor induced by an additive functor carries the canonical
shift-commuting structure inherited from the ambient termwise functor. -/
noncomputable instance commShift (F : C ⥤ D) [F.Additive] :
    (map F).CommShift ℤ :=
  inferInstanceAs (((CochainComplex.minus D).lift
    (CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex (up ℤ))
    (obj_mem F)).CommShift ℤ)

end Minus

namespace Bounded

/-- The bounded cochain functor induced by an additive functor is additive. -/
instance additive (F : C ⥤ D) [F.Additive] : (map F).Additive := sorry

/-- The bounded cochain functor induced by an additive functor carries the canonical
shift-commuting structure inherited from the ambient termwise functor. -/
noncomputable instance commShift (F : C ⥤ D) [F.Additive] :
    (map F).CommShift ℤ :=
  inferInstanceAs (((CochainComplex.bounded D).lift
    (CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex (up ℤ))
    (obj_mem F)).CommShift ℤ)

end Bounded

section Checks

variable (F : C ⥤ D) [F.Additive]

end Checks

end CategoryTheory.Functor.Cochain
