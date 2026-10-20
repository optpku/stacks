module

public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Linear
public import ReasLib.CategoryTheory.Abelian.Projective.FactorThrough
public import ReasLib.CategoryTheory.Linear.IdealProjective.Basic

@[expose] public section

/-!
# Ideal-projectivity and extension groups

@stack 0G92

Ideal-projectivity is equivalent to annihilation of every degree-one extension out of the
object.  The forward implication naturally holds in every positive degree.
-/

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe w t v u

namespace CategoryTheory.idealProjective

variable {R : Type t} [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasExt.{w} C]
variable {I : Ideal R} {X : C}

/-- An ideal-projective object has every positive-degree extension group annihilated by the
ideal. -/
theorem le_annihilator_ext (h : idealProjective (C := C) I X) (Y : C) {n : ℕ}
    (hn : 0 < n) : I ≤ Module.annihilator R (Ext X Y n) := sorry

/-- In particular, ideal-projectivity annihilates every degree-one extension group. -/
theorem le_annihilator_ext_one (h : idealProjective (C := C) I X) (Y : C) :
    I ≤ Module.annihilator R (Ext X Y 1) := sorry

/-- If the ideal annihilates all degree-one extensions out of an object, the object is
ideal-projective. -/
theorem of_ext_one_annihilator [EnoughProjectives C]
    (h : ∀ Y : C, I ≤ Module.annihilator R (Ext X Y 1)) :
    idealProjective (C := C) I X := sorry

/-- Ideal-projectivity is equivalent to annihilation of all degree-one extension groups. -/
@[stacks 0G92 "ideal-projectivity detected by Ext-one"]
theorem iff_ext_one_annihilator [EnoughProjectives C] :
    idealProjective (C := C) I X ↔
      ∀ Y : C, I ≤ Module.annihilator R (Ext X Y 1) := sorry

end CategoryTheory.idealProjective
