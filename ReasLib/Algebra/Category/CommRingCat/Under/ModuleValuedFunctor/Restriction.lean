/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.FinitePresentation
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.FilteredColimit

@[expose] public section

open CategoryTheory CommRingCat

universe u

namespace ModuleValuedFunctor

/-- A module-valued functor defined on finitely presented commutative `A`-algebras. -/
structure Restricted (A : CommRingCat.{u}) where
  /-- The module assigned to a finitely presented `A`-algebra. -/
  obj (B : FinitelyPresentedAlgebra A) : ModuleCat.{u} B.obj.right
  /-- The semilinear transition map along a morphism of finitely presented algebras. -/
  map {B B' : FinitelyPresentedAlgebra A} (f : B ⟶ B') :
    obj B ⟶ (ModuleCat.restrictScalars f.hom.right.hom).obj (obj B')
  /-- Transition along an identity morphism is the identity on elements. -/
  map_id (B : FinitelyPresentedAlgebra A) (x : obj B) : map (𝟙 B) x = x
  /-- Transition along a composite is the composite of the transition maps. -/
  map_comp {B B' B'' : FinitelyPresentedAlgebra A} (f : B ⟶ B') (g : B' ⟶ B'')
      (x : obj B) : map (f ≫ g) x = map g (map f x)

/-- Restrict a module-valued functor to finitely presented algebras. -/
def Restricted.ofGlobal {A : CommRingCat.{u}} (F : ModuleValuedFunctor.{u, u} A) :
    Restricted A where
  obj B := F.obj B.obj
  map f := F.map f.hom
  map_id B x := F.map_id B.obj x
  map_comp f g x := F.map_comp f.hom g.hom x

/-- Restriction preserves the module assigned to a finitely presented algebra. -/
theorem Restricted.ofGlobal_obj {A : CommRingCat.{u}} (F : ModuleValuedFunctor.{u, u} A)
    (B : FinitelyPresentedAlgebra A) : (Restricted.ofGlobal F).obj B = F.obj B.obj := rfl

namespace Restricted

/-- A morphism between module-valued functors on finitely presented algebras. -/
structure Hom {A : CommRingCat.{u}} (F G : Restricted A) where
  /-- The linear component over a finitely presented algebra. -/
  app (B : FinitelyPresentedAlgebra A) : F.obj B ⟶ G.obj B
  /-- The components commute with maps between finitely presented algebras. -/
  naturality {B B' : FinitelyPresentedAlgebra A} (f : B ⟶ B') (x : F.obj B) :
    G.map f (app B x) = app B' (F.map f x)

/-- Restricted morphisms are determined by their components. -/
@[ext]
theorem Hom.ext {A : CommRingCat.{u}} {F G : Restricted A} {f g : Hom F G}
    (h : ∀ B, f.app B = g.app B) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      subst g
      rfl

/-- The identity morphism of a restricted module-valued functor. -/
def Hom.id {A : CommRingCat.{u}} (F : Restricted A) : Hom F F where
  app := fun _ ↦ 𝟙 _
  naturality _ _ := rfl

/-- The identity restricted morphism acts identically on every component. -/
theorem Hom.id_app {A : CommRingCat.{u}} (F : Restricted A)
    (B : FinitelyPresentedAlgebra A) : (Hom.id F).app B = 𝟙 _ := rfl

/-- Compose morphisms of restricted module-valued functors. -/
def Hom.comp {A : CommRingCat.{u}} {F G H : Restricted A}
    (f : Hom F G) (g : Hom G H) : Hom F H where
  app B := f.app B ≫ g.app B
  naturality := by
    intro B B' h x
    change H.map h (g.app B (f.app B x)) = g.app B' (f.app B' (F.map h x))
    rw [g.naturality, f.naturality]

/-- Composition of restricted morphisms is computed componentwise. -/
theorem Hom.comp_app {A : CommRingCat.{u}} {F G H : Restricted A}
    (f : Hom F G) (g : Hom G H) (B : FinitelyPresentedAlgebra A) :
    (Hom.comp f g).app B = f.app B ≫ g.app B := rfl

/-- Restrict a morphism of global module-valued functors. -/
def Hom.ofGlobal {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}
    (f : ModuleValuedFunctor.Hom F G) : Hom (Restricted.ofGlobal F) (Restricted.ofGlobal G) where
  app B := f.app B.obj
  naturality g x := f.naturality g.hom x

/-- Restriction preserves every component of a global morphism. -/
theorem Hom.ofGlobal_app {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}
    (f : ModuleValuedFunctor.Hom F G) (B : FinitelyPresentedAlgebra A) :
    (Hom.ofGlobal f).app B = f.app B.obj := rfl

/-- The bundled category of module-valued functors on finitely presented `A`-algebras. -/
def category (A : CommRingCat.{u}) : Cat.{u + 1, u + 1} where
  α := Restricted A
  str :=
    { Hom := Hom
      id := Hom.id
      comp := Hom.comp
      id_comp := by
        intro F G f
        apply Hom.ext
        intro B
        exact Category.id_comp (f.app B)
      comp_id := by
        intro F G f
        apply Hom.ext
        intro B
        exact Category.comp_id (f.app B)
      assoc := by
        intro F G H I f g h
        apply Hom.ext
        intro B
        exact Category.assoc (f.app B) (g.app B) (h.app B) }

/-- Morphisms in `Restricted.category A` are componentwise-linear restricted morphisms. -/
theorem category_hom (A : CommRingCat.{u}) (F G : category A) :
    (F ⟶ G) = Hom F G := rfl

end Restricted

/-- The category of tensor-adequate module-valued functors on all `A`-algebras. -/
abbrev TensorAdeq (A : CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory (TensorAdequate (A := A))

/-- Every object of `TensorAdeq A` is tensor-adequate. -/
theorem TensorAdeq.adequate {A : CommRingCat.{u}} (F : TensorAdeq A) :
    TensorAdequate F.obj := F.property

/-- Restriction from tensor-adequate module-valued functors to finitely presented algebras. -/
def restriction (A : CommRingCat.{u}) : TensorAdeq A ⥤ Restricted.category A where
  obj F := Restricted.ofGlobal F.obj
  map f := Restricted.Hom.ofGlobal f.hom
  map_id F := by
    apply Restricted.Hom.ext
    intro B
    rfl
  map_comp f g := by
    apply Restricted.Hom.ext
    intro B
    rfl

/-- The restriction functor has the expected object map. -/
theorem restriction_obj (A : CommRingCat.{u}) (F : TensorAdeq A) :
    (restriction A).obj F = Restricted.ofGlobal F.obj := rfl

/-- Restriction of tensor-adequate functors is full. -/
instance restrictionFull (A : CommRingCat.{u}) : (restriction A).Full := sorry

/-- Restriction of tensor-adequate functors is faithful. -/
instance restrictionFaithful (A : CommRingCat.{u}) : (restriction A).Faithful := sorry

/-- A tensor-adequate module-valued functor is determined by its restriction to finitely
presented algebras, on both objects and morphisms. -/
theorem restrictionFullyFaithful (A : CommRingCat.{u}) :
    Nonempty (restriction A).FullyFaithful := by
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective (restriction A)).2
  intro F G
  exact ⟨(restriction A).map_injective, (restriction A).map_surjective⟩

end ModuleValuedFunctor
