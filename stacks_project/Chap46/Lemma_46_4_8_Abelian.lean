module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import stacks_project.Chap46.Lemma_46_3_9_Cokernels

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

namespace Hom

/-- Negation of morphisms of module-valued functors is computed pointwise. -/
instance instNeg (F G : ModuleValuedFunctor.{u, v} A) : Neg (F ⟶ G) where
  neg f :=
    { app := fun B ↦ -f.app B
      naturality := sorry }

/-- Addition of morphisms of module-valued functors is computed pointwise. -/
instance instAdd (F G : ModuleValuedFunctor.{u, v} A) : Add (F ⟶ G) where
  add f g :=
    { app := fun B ↦ f.app B + g.app B
      naturality := sorry }

/-- Subtraction of morphisms of module-valued functors is computed pointwise. -/
instance instSub (F G : ModuleValuedFunctor.{u, v} A) : Sub (F ⟶ G) where
  sub f g :=
    { app := fun B ↦ f.app B - g.app B
      naturality := sorry }

/-- Morphisms of module-valued functors form an additive commutative group
under pointwise operations. -/
instance instAddCommGroup (F G : ModuleValuedFunctor.{u, v} A) : AddCommGroup (F ⟶ G) where
  add_assoc := sorry
  zero_add := sorry
  neg_add_cancel := sorry
  add_zero := sorry
  add_comm := sorry
  sub_eq_add_neg := sorry
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Evaluation of a sum of morphisms of module-valued functors is pointwise addition. -/
@[simp]
theorem add_app {F G : ModuleValuedFunctor.{u, v} A} (f g : F ⟶ G) (B : Under A) :
    (f + g).app B = f.app B + g.app B := sorry

/-- Evaluation of the negative of a morphism of module-valued functors is pointwise negation. -/
@[simp]
theorem neg_app {F G : ModuleValuedFunctor.{u, v} A} (f : F ⟶ G) (B : Under A) :
    (-f).app B = -f.app B := sorry

end Hom

/-- The category of module-valued functors is preadditive under pointwise addition. -/
instance instPreadditive : Preadditive (ModuleValuedFunctor.{u, v} A) where
  homGroup F G := Hom.instAddCommGroup F G
  add_comp := sorry
  comp_add := sorry

/-- Module-valued functors form an abelian category. -/
noncomputable instance instAbelian : Abelian (ModuleValuedFunctor.{u, v} A) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := inferInstance
  has_cokernels := inferInstance

/-- The standard universe construction supplies Ext groups for module-valued functors. -/
instance instHasExt : HasExt.{max (u + 1) (v + 1)} (ModuleValuedFunctor.{u, v} A) :=
  HasExt.standard _

end ModuleValuedFunctor
