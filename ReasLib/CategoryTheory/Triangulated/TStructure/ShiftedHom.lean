module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shifted Morphisms and T-Structure Bounds

@stack 06XS

This leaf records the generic orthogonality consequence for shifted morphisms
between an object bounded above and an object bounded below. It is independent
of derived categories and of any particular realization of a t-structure.
-/

universe v u

namespace CategoryTheory.Triangulated.TStructure

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [Pretriangulated C]

/-- Stacks 06XS: shifted morphisms below the gap between an upper and a lower
t-structure bound form a subsingleton. -/
@[stacks 06XS]
theorem shiftedHom_subsingleton_of_isLE_of_isGE (t : TStructure C)
    (X Y : C) (a b n : ℤ) (hX : t.IsLE X a) (hY : t.IsGE Y b)
    (hn : n < b - a) :
    Subsingleton (ShiftedHom X Y n) := sorry

end CategoryTheory.Triangulated.TStructure
