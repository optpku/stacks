/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Zero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive categories of bimodule objects

If tensoring is additive in the ambient category, the sum of two bimodule morphisms is again a
bimodule morphism.  This file equips every fixed category of bimodule objects with its canonical
preadditive structure and records that the forgetful functor is additive.
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.Bimod

open CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {A B : Mon C} {M N : Bimod A B}

/-- The sum of two carrier maps satisfies the left-action compatibility condition. -/
theorem add_left_act_hom (f g : M ⟶ N) :
    M.actLeft ≫ (f.hom + g.hom) = (A.X ◁ (f.hom + g.hom)) ≫ N.actLeft := sorry

/-- The sum of two carrier maps satisfies the right-action compatibility condition. -/
theorem add_right_act_hom (f g : M ⟶ N) :
    M.actRight ≫ (f.hom + g.hom) = ((f.hom + g.hom) ▷ B.X) ≫ N.actRight := sorry

/-- Addition of bimodule morphisms is induced by addition of their carrier maps. -/
instance homAdd : Add (M ⟶ N) where
  add f g :=
    { hom := f.hom + g.hom
      left_act_hom := add_left_act_hom f g
      right_act_hom := add_right_act_hom f g }

/-- The carrier map of a sum of bimodule morphisms is the sum of the carrier maps. -/
@[simp]
theorem add_hom (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := sorry

/-- The negative of a carrier map satisfies the left-action compatibility condition. -/
theorem neg_left_act_hom (f : M ⟶ N) :
    M.actLeft ≫ (-f.hom) = (A.X ◁ (-f.hom)) ≫ N.actLeft := sorry

/-- The negative of a carrier map satisfies the right-action compatibility condition. -/
theorem neg_right_act_hom (f : M ⟶ N) :
    M.actRight ≫ (-f.hom) = ((-f.hom) ▷ B.X) ≫ N.actRight := sorry

/-- Negation of bimodule morphisms is induced by negation of their carrier maps. -/
instance homNeg : Neg (M ⟶ N) where
  neg f :=
    { hom := -f.hom
      left_act_hom := neg_left_act_hom f
      right_act_hom := neg_right_act_hom f }

/-- The carrier map of the negative of a bimodule morphism is the negative carrier map. -/
@[simp]
theorem neg_hom (f : M ⟶ N) : (-f).hom = -f.hom := sorry

/-- The difference of two carrier maps satisfies the left-action compatibility condition. -/
theorem sub_left_act_hom (f g : M ⟶ N) :
    M.actLeft ≫ (f.hom - g.hom) = (A.X ◁ (f.hom - g.hom)) ≫ N.actLeft := sorry

/-- The difference of two carrier maps satisfies the right-action compatibility condition. -/
theorem sub_right_act_hom (f g : M ⟶ N) :
    M.actRight ≫ (f.hom - g.hom) = ((f.hom - g.hom) ▷ B.X) ≫ N.actRight := sorry

/-- Subtraction of bimodule morphisms is induced by subtraction of their carrier maps. -/
instance homSub : Sub (M ⟶ N) where
  sub f g :=
    { hom := f.hom - g.hom
      left_act_hom := sub_left_act_hom f g
      right_act_hom := sub_right_act_hom f g }

/-- The carrier map of a difference of bimodule morphisms is the difference of the carrier maps. -/
@[simp]
theorem sub_hom (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := sorry

/-- A natural-number multiple of a carrier map satisfies left-action compatibility. -/
theorem nsmul_left_act_hom (n : ℕ) (f : M ⟶ N) :
    M.actLeft ≫ (n • f.hom) = (A.X ◁ (n • f.hom)) ≫ N.actLeft := sorry

/-- A natural-number multiple of a carrier map satisfies right-action compatibility. -/
theorem nsmul_right_act_hom (n : ℕ) (f : M ⟶ N) :
    M.actRight ≫ (n • f.hom) = ((n • f.hom) ▷ B.X) ≫ N.actRight := sorry

/-- Natural-number scalar multiplication of bimodule morphisms is induced on carrier maps. -/
instance homNatSMul : SMul ℕ (M ⟶ N) where
  smul n f :=
    { hom := n • f.hom
      left_act_hom := nsmul_left_act_hom n f
      right_act_hom := nsmul_right_act_hom n f }

/-- The carrier map of a natural-number multiple is the corresponding multiple. -/
@[simp]
theorem nsmul_hom (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := sorry

/-- An integer multiple of a carrier map satisfies left-action compatibility. -/
theorem zsmul_left_act_hom (n : ℤ) (f : M ⟶ N) :
    M.actLeft ≫ (n • f.hom) = (A.X ◁ (n • f.hom)) ≫ N.actLeft := sorry

/-- An integer multiple of a carrier map satisfies right-action compatibility. -/
theorem zsmul_right_act_hom (n : ℤ) (f : M ⟶ N) :
    M.actRight ≫ (n • f.hom) = ((n • f.hom) ▷ B.X) ≫ N.actRight := sorry

/-- Integer scalar multiplication of bimodule morphisms is induced on carrier maps. -/
instance homIntSMul : SMul ℤ (M ⟶ N) where
  smul n f :=
    { hom := n • f.hom
      left_act_hom := zsmul_left_act_hom n f
      right_act_hom := zsmul_right_act_hom n f }

/-- The carrier map of an integer multiple is the corresponding multiple. -/
@[simp]
theorem zsmul_hom (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := sorry

/-- The carrier-map projection is injective on bimodule morphisms. -/
theorem hom_injective :
    Function.Injective (fun f : M ⟶ N ↦ f.hom) := sorry

/-- Bimodule morphisms form an additive commutative group under pointwise operations. -/
instance homAddCommGroup : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (fun f : M ⟶ N ↦ f.hom) hom_injective
    (zero_hom M N) (fun _ _ ↦ add_hom _ _) (fun _ ↦ neg_hom _)
      (fun _ _ ↦ sub_hom _ _) (fun _ _ ↦ nsmul_hom _ _)
        (fun _ _ ↦ zsmul_hom _ _)

/-- Fixed bimodule categories inherit the canonical preadditive structure of the ambient
monoidal category. -/
@[stacks 0FSC "preadditive category of bimodule objects"]
instance instPreadditive : Preadditive (Bimod A B) where
  homGroup := fun _ _ ↦ homAddCommGroup
  add_comp := sorry
  comp_add := sorry

/-- The forgetful functor from bimodule objects to the ambient category is additive. -/
@[stacks 0FSC "additive forgetful functor from bimodule objects"]
instance forgetAdditive : (_root_.Bimod.forget (B := B) A).Additive := sorry

end CategoryTheory.Bimod

end
