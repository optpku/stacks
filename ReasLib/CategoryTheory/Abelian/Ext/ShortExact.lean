/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

@[expose] public section

/-!
# Extension-class lifting criteria

@stack 0G92
@stack 0G95

For a short exact sequence, vanishing of the Yoneda product with its extension class is exactly
the obstruction to lifting a morphism through the middle term.  Both covariant and
contravariant versions are exposed symmetrically.
-/

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe w v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {S : ShortComplex C}

/-- A map into the cokernel object lifts through the middle term iff its pullback of the
extension class vanishes. -/
@[stacks 0G92 "Ext obstruction to lifting into the middle term"]
theorem mk₀_comp_extClass_eq_zero_iff (hS : S.ShortExact) {X : C} (f : X ⟶ S.X₃) :
    (mk₀ f).comp hS.extClass (zero_add 1) = 0 ↔
      ∃ g : X ⟶ S.X₂, g ≫ S.g = f := sorry

/-- A map out of the kernel object extends through the middle term iff its product with the
extension class vanishes. -/
@[stacks 0G95 "Ext obstruction to extending from the kernel term"]
theorem extClass_comp_mk₀_eq_zero_iff (hS : S.ShortExact) {Y : C} (f : S.X₁ ⟶ Y) :
    hS.extClass.comp (mk₀ f) (add_zero 1) = 0 ↔
      ∃ g : S.X₂ ⟶ Y, S.f ≫ g = f := sorry

end CategoryTheory.ShortComplex.ShortExact
