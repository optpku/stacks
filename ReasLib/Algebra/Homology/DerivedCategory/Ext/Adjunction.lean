/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Adjunction.ExactFunctor

@[expose] public section

/-!
# Ext along an exact adjunction

An adjunction between abelian categories gives comparison maps between Ext
groups.  When both adjoints are exact, these maps are inverse additive
equivalences.  This file owns that categorical construction independently of
any particular change-of-rings model.
-/

noncomputable section

open CategoryTheory Limits Abelian

universe w w' v v' u u'

namespace CategoryTheory.Adjunction.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable {L : C ⥤ D} {R : D ⥤ C}

section Comparison

variable [PreservesFiniteColimits R]

/-- The Ext comparison induced by applying the exact right adjoint and
precomposing with the adjunction unit. -/
@[stacks 087N "Ext comparison of an exact adjunction"]
noncomputable def comparison (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ) :
    Ext.{w'} (L.obj X) Y n →+ Ext.{w} X (R.obj Y) n :=
  ((Ext.mk₀ (adj.unit.app X)).precomp (R.obj Y) (zero_add n)).comp
    ((adj.exactRightAdjoint).obj.mapExtAddHom (L.obj X) Y n)

/-- The Ext comparison is contravariantly natural in its source object. -/
@[simp, stacks 087N "Ext comparison naturality in the source"]
theorem comparison_naturality_left (adj : L ⊣ R) {X X' : C} (f : X' ⟶ X)
    {Y : D} {n : ℕ} (e : Ext.{w'} (L.obj X) Y n) :
    comparison adj X' Y n ((Ext.mk₀ (L.map f)).comp e (zero_add n)) =
      (Ext.mk₀ f).comp (comparison adj X Y n e) (zero_add n) := sorry

/-- The Ext comparison is covariantly natural in its target object. -/
@[simp, stacks 087N "Ext comparison naturality in the target"]
theorem comparison_naturality_right (adj : L ⊣ R) {X : C} {Y Y' : D}
    {n : ℕ} (e : Ext.{w'} (L.obj X) Y n) (g : Y ⟶ Y') :
    comparison adj X Y' n (e.comp (Ext.mk₀ g) (add_zero n)) =
      (comparison adj X Y n e).comp (Ext.mk₀ (R.map g)) (add_zero n) := sorry

/-- Precomposing by the counit identifies the Ext comparison with the exact-functor map of the
right adjoint. -/
@[stacks 087N "Ext comparison and counit bridge"]
theorem comparison_precomp_counit (adj : L ⊣ R) (Y Z : D) {n : ℕ}
    (e : Ext.{w'} Y Z n) :
    comparison adj (R.obj Y) Z n
        ((Ext.mk₀ (adj.counit.app Y)).comp e (zero_add n)) =
      (adj.exactRightAdjoint).obj.mapExtAddHom Y Z n e := sorry

end Comparison

section Adjoint

variable [PreservesFiniteLimits L]

/-- The inverse-direction Ext comparison induced by applying the exact left
adjoint and postcomposing with the adjunction counit. -/
@[stacks 087N "inverse Ext comparison of an exact adjunction"]
noncomputable def adjoint (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ) :
    Ext.{w} X (R.obj Y) n →+ Ext.{w'} (L.obj X) Y n :=
  ((Ext.mk₀ (adj.counit.app Y)).postcomp (L.obj X) (add_zero n)).comp
    ((adj.exactLeftAdjoint).obj.mapExtAddHom X (R.obj Y) n)

/-- The inverse-direction Ext comparison is contravariantly natural in its source object. -/
@[simp, stacks 087N "Ext adjoint naturality in the source"]
theorem adjoint_naturality_left (adj : L ⊣ R) {X X' : C} (f : X' ⟶ X)
    {Y : D} {n : ℕ} (e : Ext.{w} X (R.obj Y) n) :
    adjoint adj X' Y n ((Ext.mk₀ f).comp e (zero_add n)) =
      (Ext.mk₀ (L.map f)).comp (adjoint adj X Y n e) (zero_add n) := sorry

/-- The inverse-direction Ext comparison is covariantly natural in its target object. -/
@[simp, stacks 087N "Ext adjoint naturality in the target"]
theorem adjoint_naturality_right (adj : L ⊣ R) {X : C} {Y Y' : D}
    {n : ℕ} (e : Ext.{w} X (R.obj Y) n) (g : Y ⟶ Y') :
    adjoint adj X Y' n
        (e.comp (Ext.mk₀ (R.map g)) (add_zero n)) =
      (adjoint adj X Y n e).comp (Ext.mk₀ g) (add_zero n) := sorry

/-- Postcomposing by the unit identifies the inverse-direction Ext comparison with the
exact-functor map of the left adjoint. -/
@[stacks 087N "Ext adjoint and unit bridge"]
theorem adjoint_postcomp_unit (adj : L ⊣ R) (X Z : C) {n : ℕ}
    (e : Ext.{w} X Z n) :
    adjoint adj X (L.obj Z) n
        (e.comp (Ext.mk₀ (adj.unit.app Z)) (add_zero n)) =
      (adj.exactLeftAdjoint).obj.mapExtAddHom X Z n e := sorry

end Adjoint

section Equiv

variable [PreservesFiniteLimits L]
variable [PreservesFiniteColimits R]

/-- Applying the two exact adjoints and then the adjunction unit and counit is
the identity on Ext in the left-adjoint category. -/
@[simp, stacks 087N "Ext adjunction left inverse"]
theorem adjoint_comparison (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ)
    (x : Ext.{w'} (L.obj X) Y n) :
    adjoint adj X Y n (comparison adj X Y n x) = x := sorry

/-- Applying the two exact adjoints and then the adjunction unit and counit is
the identity on Ext in the right-adjoint category. -/
@[simp, stacks 087N "Ext adjunction right inverse"]
theorem comparison_adjoint (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ)
    (x : Ext.{w} X (R.obj Y) n) :
    comparison adj X Y n (adjoint adj X Y n x) = x := sorry

/-- An exact adjunction induces an additive equivalence on Ext groups. -/
@[stacks 087N "Ext equivalence of an exact adjunction"]
noncomputable def equiv (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ) :
    Ext.{w'} (L.obj X) Y n ≃+ Ext.{w} X (R.obj Y) n where
  toFun := comparison adj X Y n
  invFun := adjoint adj X Y n
  left_inv := adjoint_comparison adj X Y n
  right_inv := comparison_adjoint adj X Y n
  map_add' := (comparison adj X Y n).map_add

/-- The forward map of the Ext equivalence is the unit comparison. -/
@[simp, stacks 087N "Ext equivalence forward map"]
theorem equiv_apply (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ)
    (x : Ext.{w'} (L.obj X) Y n) :
    equiv adj X Y n x = comparison adj X Y n x := sorry

/-- The inverse map of the Ext equivalence is the counit comparison. -/
@[simp, stacks 087N "Ext equivalence inverse map"]
theorem equiv_symm_apply (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ)
    (x : Ext.{w} X (R.obj Y) n) :
    (equiv adj X Y n).symm x = adjoint adj X Y n x := sorry

end Equiv

end CategoryTheory.Adjunction.Ext
