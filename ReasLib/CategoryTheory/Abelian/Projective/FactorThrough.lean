/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Projective.Ext
public import ReasLib.CategoryTheory.ObjectProperty.FactorThrough

@[expose] public section

/-!
# Projective factorisation detected by `Ext¹`

In an abelian category with enough projectives, a morphism factors through a projective object
exactly when precomposition by that morphism kills every degree-one extension.  This is the
generic obstruction theorem behind ideal-projectivity criteria for modules.
@stack 0G92
-/

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe w v u

namespace CategoryTheory.Projective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A morphism factors through a projective object iff it annihilates every `Ext¹` class by
precomposition. -/
@[stacks 0G92 "projective factorisation detected by Ext-one"]
theorem factorThru_iff_ext_one [EnoughProjectives C] {X Y : C} (f : X ⟶ Y) :
    (isProjective C).factorThru f ↔
      ∀ (Z : C) (e : Ext Y Z 1), (mk₀ f).comp e (zero_add 1) = 0 := sorry

end CategoryTheory.Projective
