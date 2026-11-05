/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Category

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- Pointwise addition of bundled module-valued-functor morphisms. -/
@[reducible] def bundledHomAdd (A : CommRingCat.{u}) (F G : bundled.{u, v} A) : Add (F ⟶ G) where
  add f g :=
    { app := fun B ↦ f.app B + g.app B
      naturality := by
        intro B B' h x
        change G.map h ((f.app B).hom x + (g.app B).hom x) =
          ((f.app B').hom + (g.app B').hom) (F.map h x)
        have hf : G.map h ((f.app B).hom x) = (f.app B').hom (F.map h x) :=
          f.naturality h x
        have hg : G.map h ((g.app B).hom x) = (g.app B').hom (F.map h x) :=
          g.naturality h x
        rw [map_add, hf, hg, LinearMap.add_apply]
        rfl }

/-- Pointwise negation of bundled module-valued-functor morphisms. -/
@[reducible] def bundledHomNeg (A : CommRingCat.{u}) (F G : bundled.{u, v} A) : Neg (F ⟶ G) where
  neg f :=
    { app := fun B ↦ -f.app B
      naturality := by
        intro B B' h x
        change G.map h (-(f.app B).hom x) = (-((f.app B').hom)) (F.map h x)
        have hf : G.map h ((f.app B).hom x) = (f.app B').hom (F.map h x) :=
          f.naturality h x
        rw [map_neg, hf, LinearMap.neg_apply]
        rfl }

/-- The pointwise zero bundled module-valued-functor morphism. -/
@[reducible]
def bundledHomZero (A : CommRingCat.{u}) (F G : bundled.{u, v} A) : Zero (F ⟶ G) where
  zero :=
    { app := fun _ ↦ 0
      naturality := by
        intro B B' f x
        change _ = (0 : G.obj B')
        exact map_zero (G.map f).hom }

/-- The pointwise additive commutative group structure on morphisms in the bundled
category of module-valued functors. -/
@[reducible] def bundledHomAddCommGroup (A : CommRingCat.{u}) (F G : bundled.{u, v} A) :
    AddCommGroup (F ⟶ G) where
  add := (bundledHomAdd A F G).add
  zero := (bundledHomZero A F G).zero
  neg := (bundledHomNeg A F G).neg
  sub f g := (bundledHomAdd A F G).add f ((bundledHomNeg A F G).neg g)
  add_assoc := by
    intros
    apply hom_ext
    intro B
    exact add_assoc _ _ _
  zero_add := by
    intros
    apply hom_ext
    intro B
    exact zero_add _
  add_zero := by
    intros
    apply hom_ext
    intro B
    exact add_zero _
  add_comm := by
    intros
    apply hom_ext
    intro B
    exact add_comm _ _
  neg_add_cancel := by
    intros
    apply hom_ext
    intro B
    exact neg_add_cancel _
  sub_eq_add_neg := by
    intros
    rfl
  nsmul := @nsmulRec _ (bundledHomZero A F G) (bundledHomAdd A F G)
  zsmul := @zsmulRec _ (bundledHomZero A F G) (bundledHomAdd A F G)
    (bundledHomNeg A F G) (@nsmulRec _ (bundledHomZero A F G) (bundledHomAdd A F G))
  nsmul_zero := by intro; rfl
  nsmul_succ := by intros; rfl
  zsmul_zero' := by intro; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl

/-- The bundled module-valued-functor category is canonically preadditive. -/
@[reducible]
def bundledPreadditive (A : CommRingCat.{u}) : Preadditive (bundled.{u, v} A) where
  homGroup F G := bundledHomAddCommGroup A F G
  add_comp F G H f g h := by
    apply hom_ext
    intro B
    change (f.app B + g.app B) ≫ h.app B = f.app B ≫ h.app B + g.app B ≫ h.app B
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add F G H f g h := by
    apply hom_ext
    intro B
    change f.app B ≫ (g.app B + h.app B) = f.app B ≫ g.app B + f.app B ≫ h.app B
    exact Preadditive.comp_add _ _ _ _ _ _

/-- The bundled module-valued-functor category is abelian. -/
@[reducible]
noncomputable def bundledAbelian (A : CommRingCat.{u}) : Abelian (bundled.{u, v} A) := by
  letI := bundledPreadditive.{u, v} A
  letI : HasFiniteProducts (bundled.{u, v} A) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence (presheafEquivalence A).functor⟩
  exact abelianOfEquivalence (presheafEquivalence A).functor

/-- The standard universe construction supplies Ext groups for the bundled
module-valued-functor category. -/
@[reducible] noncomputable def bundledHasExt (A : CommRingCat.{u}) :=
  @HasExt.standard (bundled.{u, v} A) (bundled.{u, v} A).str (bundledAbelian A)

end ModuleValuedFunctor
