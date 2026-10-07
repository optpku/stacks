module

public import ReasLib.CategoryTheory.Bicategory.StrictSlice
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object properties on strict slices

An object property on a bicategory induces the property that the domain of a
strict-slice object satisfies it.  This is the canonical owner for strict
slices of full subbicategories.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

open Bicategory
open scoped Bicategory

variable {D : Type u} [Bicategory.{w, v} D] [Bicategory.Strict D]

/-- The object property on `StrictSlice X` obtained by requiring its domain to
satisfy `P`. -/
def strictSlice (P : ObjectProperty D) (X : D) :
    ObjectProperty (StrictSlice X) :=
  fun S => P S.obj

/-- Membership in `P.strictSlice X` is exactly membership of the domain in
`P`. -/
@[simp]
theorem prop_strictSlice_iff (P : ObjectProperty D) (X : D)
    (S : StrictSlice X) :
    P.strictSlice X S ↔ P S.obj := sorry

end CategoryTheory.ObjectProperty
