/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.CategoryTheory.InverseSystem.Milnor

@[expose] public section

/-!
# Inverse Limits as Kernels of Milnor Difference Maps

This leaf identifies the inverse limit of a sequential inverse system with the
kernel of its Milnor difference map.  The factorization of a morphism through
the inverse limit is built from an explicit cone whose stage maps are the
composites with the product projections.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem.Milnor

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The canonical morphism from the inverse limit of a sequential inverse system to the
product of its stages. -/
@[stacks 08TC]
def limitToProduct (K : SequentialInverseSystem C) [HasProduct K.family] [HasLimit K] :
    limit K ⟶ ∏ᶜ K.family :=
  Pi.lift fun n ↦ limit.π K (op n)

/-- The component of `limitToProduct` at stage `n` is the canonical limit projection. -/
@[reassoc (attr := simp)]
theorem limitToProduct_comp_π (K : SequentialInverseSystem C) [HasProduct K.family]
    [HasLimit K] (n : ℕ) :
    limitToProduct K ≫ Pi.π K.family n = limit.π K (op n) := by
  exact limit.lift_π _ _

/-- The canonical map from the inverse limit is annihilated by the Milnor difference map. -/
@[reassoc, stacks 08TC]
theorem limitToProduct_comp_milnorDifferenceMap (K : SequentialInverseSystem C)
    [HasProduct K.family] [HasLimit K] :
    limitToProduct K ≫ K.milnorDifferenceMap = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, milnorDifferenceMap, Preadditive.sub_comp,
    Category.id_comp, Pi.map'_comp_π, Preadditive.comp_sub,
    limitToProduct_comp_π, limitToProduct_comp_π_assoc, zero_comp]
  exact sub_eq_zero.mpr (limit.w K (homOfLE (Nat.le_succ n)).op).symm

/-- The stage map determined by a morphism into the product of a sequential inverse system. -/
def kernelConeApp (K : SequentialInverseSystem C) [HasProduct K.family] {W : C}
    (f : W ⟶ ∏ᶜ K.family) (n : ℕ) : W ⟶ K.obj (op n) :=
  f ≫ Pi.π K.family n

/-- A morphism annihilated by the Milnor difference map has compatible stage maps.  This is
the successor naturality equation in the form required by `NatTrans.ofOpSequence`. -/
theorem kernelConeApp_naturality (K : SequentialInverseSystem C) [HasProduct K.family]
    {W : C} (f : W ⟶ ∏ᶜ K.family) (h : f ≫ K.milnorDifferenceMap = 0) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj W).map (homOfLE (Nat.le_add_right n 1)).op ≫
        kernelConeApp K f n =
      kernelConeApp K f (n + 1) ≫ K.transitionMap (Nat.le_add_right n 1) := by
  change 𝟙 W ≫ (f ≫ Pi.π K.family n) =
    (f ≫ Pi.π K.family (n + 1)) ≫ K.transitionMap (Nat.le_add_right n 1)
  rw [Category.id_comp]
  apply sub_eq_zero.mp
  have hn := congrArg (fun g ↦ g ≫ Pi.π K.family n) h
  simpa only [Category.assoc, milnorDifferenceMap, Preadditive.sub_comp,
    Category.id_comp, Pi.map'_comp_π, Preadditive.comp_sub, zero_comp] using hn

/-- The natural transformation whose components are the stage maps of a morphism annihilated
by the Milnor difference map. -/
def kernelConeNatTrans (K : SequentialInverseSystem C) [HasProduct K.family] {W : C}
    (f : W ⟶ ∏ᶜ K.family) (h : f ≫ K.milnorDifferenceMap = 0) :
    (Functor.const ℕᵒᵖ).obj W ⟶ K :=
  NatTrans.ofOpSequence (kernelConeApp K f) (kernelConeApp_naturality K f h)

/-- The component of `kernelConeNatTrans` is composition with the corresponding product
projection. -/
@[simp]
theorem kernelConeNatTrans_app (K : SequentialInverseSystem C) [HasProduct K.family]
    {W : C} (f : W ⟶ ∏ᶜ K.family) (h : f ≫ K.milnorDifferenceMap = 0) (n : ℕ) :
    (kernelConeNatTrans K f h).app (op n) = f ≫ Pi.π K.family n := by
  rfl

/-- The explicit cone over a sequential inverse system determined by a morphism into its
product that is annihilated by the Milnor difference map. -/
def kernelCone (K : SequentialInverseSystem C) [HasProduct K.family] {W : C}
    (f : W ⟶ ∏ᶜ K.family) (h : f ≫ K.milnorDifferenceMap = 0) : Cone K where
  pt := W
  π := kernelConeNatTrans K f h

/-- The projection of `kernelCone` at stage `n` is composition with the corresponding product
projection. -/
@[simp]
theorem kernelCone_π_app (K : SequentialInverseSystem C) [HasProduct K.family]
    {W : C} (f : W ⟶ ∏ᶜ K.family) (h : f ≫ K.milnorDifferenceMap = 0) (n : ℕ) :
    (kernelCone K f h).π.app (op n) = f ≫ Pi.π K.family n := by
  rfl

/-- The explicit lift to the inverse limit of a morphism annihilated by the Milnor difference
map. -/
@[stacks 08TC]
def liftToLimit (K : SequentialInverseSystem C) [HasProduct K.family] [HasLimit K]
    {W : C} (f : W ⟶ ∏ᶜ K.family) (h : f ≫ K.milnorDifferenceMap = 0) :
    W ⟶ limit K :=
  limit.lift K (kernelCone K f h)

/-- The lift to the inverse limit has the prescribed component at every stage. -/
@[reassoc (attr := simp)]
theorem liftToLimit_comp_π (K : SequentialInverseSystem C) [HasProduct K.family]
    [HasLimit K] {W : C} (f : W ⟶ ∏ᶜ K.family)
    (h : f ≫ K.milnorDifferenceMap = 0) (n : ℕ) :
    liftToLimit K f h ≫ limit.π K (op n) = f ≫ Pi.π K.family n := by
  exact limit.lift_π _ _

/-- The lift to the inverse limit factors the original morphism through `limitToProduct`. -/
@[reassoc]
theorem liftToLimit_fac (K : SequentialInverseSystem C) [HasProduct K.family]
    [HasLimit K] {W : C} (f : W ⟶ ∏ᶜ K.family)
    (h : f ≫ K.milnorDifferenceMap = 0) :
    liftToLimit K f h ≫ limitToProduct K = f := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, limitToProduct_comp_π, liftToLimit_comp_π]

/-- A morphism into the inverse limit is determined by its composite with `limitToProduct`. -/
theorem liftToLimit_uniq (K : SequentialInverseSystem C) [HasProduct K.family]
    [HasLimit K] {W : C} (f : W ⟶ ∏ᶜ K.family)
    (h : f ≫ K.milnorDifferenceMap = 0) (m : W ⟶ limit K)
    (hm : m ≫ limitToProduct K = f) :
    m = liftToLimit K f h := by
  apply limit.hom_ext
  intro n
  obtain ⟨n⟩ := n
  rw [liftToLimit_comp_π, ← hm, Category.assoc, limitToProduct_comp_π]

/-- The canonical kernel fork of the Milnor difference map whose point is the inverse limit. -/
@[stacks 08TC]
def limitKernelFork (K : SequentialInverseSystem C) [HasProduct K.family] [HasLimit K] :
    KernelFork K.milnorDifferenceMap :=
  KernelFork.ofι (limitToProduct K) (limitToProduct_comp_milnorDifferenceMap K)

/-- The inclusion of `limitKernelFork` is the canonical map from the inverse limit to the
product of stages. -/
@[simp]
theorem limitKernelFork_ι (K : SequentialInverseSystem C) [HasProduct K.family]
    [HasLimit K] :
    (limitKernelFork K).ι = limitToProduct K := by
  rfl

/-- The explicit universal property exhibiting the inverse limit as the kernel of the Milnor
difference map. Its lift is `liftToLimit`, with factorization and uniqueness supplied by
`liftToLimit_fac` and `liftToLimit_uniq`. -/
@[stacks 08TC]
def limitKernelForkIsLimit (K : SequentialInverseSystem C) [HasProduct K.family]
    [HasLimit K] : IsLimit (limitKernelFork K) :=
  KernelFork.IsLimit.ofι (limitToProduct K)
    (limitToProduct_comp_milnorDifferenceMap K)
    (fun {_} f h ↦ liftToLimit K f h)
    (fun {_} f h ↦ liftToLimit_fac K f h)
    (fun {_} f h m hm ↦ liftToLimit_uniq K f h m hm)

/-- The universal lift supplied by `limitKernelForkIsLimit` is the explicit map
`liftToLimit`. -/
@[simp]
theorem limitKernelForkIsLimit_lift (K : SequentialInverseSystem C)
    [HasProduct K.family] [HasLimit K] {W : C}
    (f : W ⟶ ∏ᶜ K.family) (h : f ≫ K.milnorDifferenceMap = 0) :
    (limitKernelForkIsLimit K).lift (KernelFork.ofι f h) = liftToLimit K f h := by
  rfl

end CategoryTheory.SequentialInverseSystem.Milnor
