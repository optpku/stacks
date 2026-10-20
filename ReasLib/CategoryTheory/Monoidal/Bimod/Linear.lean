/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear categories of bimodule objects

For a monoidal `R`-linear category whose tensor product is linear in each variable, scalar
multiplication of carrier maps preserves both bimodule actions.  Thus every fixed category of
bimodule objects is canonically `R`-linear.
-/

@[expose] public section

noncomputable section

universe w u v

namespace CategoryTheory.Bimod

open CategoryTheory.MonoidalCategory

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C]
variable {A B : Mon C} {M N : Bimod A B}

/-- A scalar multiple of a carrier map satisfies the left-action compatibility condition. -/
theorem smul_left_act_hom (r : R) (f : M ⟶ N) :
    M.actLeft ≫ (r • f.hom) = (A.X ◁ (r • f.hom)) ≫ N.actLeft := sorry

/-- A scalar multiple of a carrier map satisfies the right-action compatibility condition. -/
theorem smul_right_act_hom (r : R) (f : M ⟶ N) :
    M.actRight ≫ (r • f.hom) = ((r • f.hom) ▷ B.X) ≫ N.actRight := sorry

/-- Scalar multiplication of bimodule morphisms is induced on carrier maps.

The lower priority leaves the canonical natural- and integer-multiple operations from the
preadditive structure in charge when they apply.
-/
instance (priority := 900) homSMul : SMul R (M ⟶ N) where
  smul r f :=
    { hom := r • f.hom
      left_act_hom := smul_left_act_hom r f
      right_act_hom := smul_right_act_hom r f }

/-- The carrier map of a scalar multiple is the corresponding scalar multiple. -/
@[simp]
theorem smul_hom (r : R) (f : M ⟶ N) : (r • f).hom = r • f.hom := sorry

/-- Bimodule morphisms inherit the ambient module structure through their carrier maps. -/
instance homModule : Module R (M ⟶ N) :=
  Function.Injective.module R
    { toFun := fun f : M ⟶ N ↦ f.hom
      map_zero' := zero_hom M N
      map_add' := add_hom }
    hom_injective (fun _ _ ↦ smul_hom _ _)

/-- Fixed bimodule categories inherit the canonical linear structure of the ambient monoidal
category. -/
@[stacks 0FSC "linear category of bimodule objects"]
instance instLinear : Linear R (Bimod A B) where
  homModule := fun _ _ ↦ homModule
  smul_comp := sorry
  comp_smul := sorry

/-- The forgetful functor from bimodule objects to the ambient category is linear. -/
@[stacks 0FSC "linear forgetful functor from bimodule objects"]
instance forgetLinear :
    Functor.Linear R (_root_.Bimod.forget (B := B) A) := sorry

#synth Linear R (Bimod A B)
#synth Functor.Linear R (_root_.Bimod.forget (B := B) A)

end CategoryTheory.Bimod

end
