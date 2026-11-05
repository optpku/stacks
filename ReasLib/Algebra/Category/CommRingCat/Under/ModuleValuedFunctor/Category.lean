/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- The identity morphism of a module-valued functor. -/
def Hom.id (F : ModuleValuedFunctor.{u, v} A) : Hom F F where
  app := fun _ ↦ 𝟙 _
  naturality := by intros; rfl

/-- The composite of morphisms of module-valued functors. -/
def Hom.comp {F G H : ModuleValuedFunctor.{u, v} A} (f : Hom F G) (g : Hom G H) : Hom F H where
  app := fun B ↦ f.app B ≫ g.app B
  naturality := by
    intro B B' h x
    change H.map h (g.app B (f.app B x)) = g.app B' (f.app B' (F.map h x))
    rw [g.naturality, f.naturality]

/-- The category structure on module-valued functors whose morphisms have linear components
over every algebra. -/
@[reducible]
def category : Category (ModuleValuedFunctor.{u, v} A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; apply hom_ext; intro B; exact Category.id_comp _
  comp_id := by intros; apply hom_ext; intro B; exact Category.comp_id _
  assoc := by intros; apply hom_ext; intro B; exact Category.assoc _ _ _

/-- The category of module-valued functors with linear component morphisms. -/
def bundled (A : CommRingCat.{u}) : Cat :=
  @Cat.of (ModuleValuedFunctor.{u, v} A) category

/-- The category of module-valued functors has componentwise zero morphisms. -/
@[reducible]
def bundledHasZeroMorphisms (A : CommRingCat.{u}) :
    HasZeroMorphisms (bundled.{u, v} A) where
  zero F G :=
    { zero :=
        { app := fun _ ↦ 0
          naturality := by
            intro B B' f x
            change _ = (0 : G.obj B')
            exact map_zero (G.map f).hom } }
  comp_zero := by
    intros
    apply hom_ext
    intro B
    exact comp_zero
  zero_comp := by
    intros
    apply hom_ext
    intro B
    exact zero_comp

/-- The functor to the canonical category of module presheaves. -/
def presheafFunctor (A : CommRingCat.{u}) :
    ModuleValuedFunctor.bundled.{u, v} A ⥤ PresheafOfModules.{v} (coefficientPresheaf A) where
  obj := toPresheaf
  map f := presheafHomEquiv _ _ f
  map_id F := by
    apply PresheafOfModules.hom_ext
    intro X
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro X
    rfl

/-- The inverse functor, with the original linear components. -/
def ofPresheafFunctor (A : CommRingCat.{u}) :
    PresheafOfModules.{v} (coefficientPresheaf A) ⥤ ModuleValuedFunctor.bundled.{u, v} A where
  obj := ofPresheaf
  map f :=
    { app := fun B ↦ f.app (op (op B))
      naturality := fun g x ↦ (PresheafOfModules.naturality_apply f g.op.op x).symm }
  map_id F := by
    apply hom_ext
    intro B
    rfl
  map_comp f g := by
    apply hom_ext
    intro B
    rfl

/-- The explicit equivalence with module presheaves, preserving objects and components. -/
def presheafEquivalence (A : CommRingCat.{u}) :
    ModuleValuedFunctor.bundled.{u, v} A ≌ PresheafOfModules.{v} (coefficientPresheaf A) where
  functor := presheafFunctor A
  inverse := ofPresheafFunctor A
  unitIso := NatIso.ofComponents
    (fun F ↦ eqToIso ((presheafObjectEquiv A).left_inv F).symm)
    (fun f ↦ by apply hom_ext; intro B; rfl)
  counitIso := NatIso.ofComponents
    (fun F ↦ eqToIso ((presheafObjectEquiv A).right_inv F))
    (fun f ↦ by apply PresheafOfModules.hom_ext; intro X; rfl)
  functor_unitIso_comp F := by
    apply PresheafOfModules.hom_ext
    intro X
    rfl

/-- The equivalence preserves the specified module over each algebra. -/
@[simp] theorem presheafEquivalence_obj (F : bundled.{u, v} A) (B : Under A) :
    ((presheafEquivalence A).functor.obj F).obj (op (op B)) = F.obj B := rfl

/-- The equivalence preserves the specified linear component of each morphism. -/
@[simp] theorem presheafEquivalence_map_app {F G : bundled.{u, v} A}
    (f : F ⟶ G) (B : Under A) :
    ((presheafEquivalence A).functor.map f).app (op (op B)) = f.app B := rfl

/-- The category of module-valued functors admits kernels, supplied by the standard model. -/
theorem bundledHasKernels (A : CommRingCat.{u}) :
    @HasKernels (bundled.{u, v} A) _ (bundledHasZeroMorphisms.{u, v} A) := by
  letI := bundledHasZeroMorphisms.{u, v} A
  haveI : HasEqualizers (bundled.{u, v} A) :=
    Adjunction.hasLimitsOfShape_of_equivalence (presheafEquivalence A).functor
  infer_instance

/-- A module-valued functor is injective for the explicit category structure on
module-valued functors. -/
abbrev IsInjective (I : ModuleValuedFunctor.{u, v} A) : Prop :=
  @CategoryTheory.Injective (ModuleValuedFunctor.{u, v} A) category I

end ModuleValuedFunctor
