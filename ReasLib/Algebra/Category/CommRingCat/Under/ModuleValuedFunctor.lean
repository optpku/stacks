/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.Constructions

@[expose] public section

open CategoryTheory Opposite

universe u v

/-- A functor on `A`-algebras whose value at `B` is a `B`-module and whose map along
`f : B ⟶ B'` is `B`-linear after restriction of scalars along `f`. -/
structure ModuleValuedFunctor (A : CommRingCat.{u}) where
  /-- The module assigned to an `A`-algebra. -/
  obj (B : Under A) : ModuleCat.{v} B.right
  /-- The semilinear transition map, expressed as a linear map into restriction of scalars. -/
  map {B B' : Under A} (f : B ⟶ B') :
    obj B ⟶ (ModuleCat.restrictScalars f.right.hom).obj (obj B')
  /-- Transition along an identity morphism is the identity on elements. -/
  map_id (B : Under A) (x : obj B) : map (𝟙 B) x = x
  /-- Transition along a composite is the composite of the transition maps. -/
  map_comp {B B' B'' : Under A} (f : B ⟶ B') (g : B' ⟶ B'') (x : obj B) :
    map (f ≫ g) x = map g (map f x)

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- Forgetting the module structure sends transition along an identity to an identity. -/
theorem toFunctor_map_id (F : ModuleValuedFunctor.{u, v} A) (B : Under A) :
    (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (F.map (𝟙 B)) =
      𝟙 ((forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).obj (F.obj B)) := by
  ext x
  exact F.map_id B x

/-- Forgetting the module structure preserves composition of transition maps. -/
theorem toFunctor_map_comp (F : ModuleValuedFunctor.{u, v} A) {B B' B'' : Under A}
    (f : B ⟶ B') (g : B' ⟶ B'') :
    (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (F.map (f ≫ g)) =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (F.map f) ≫
        (forget₂ (ModuleCat.{v} B'.right) AddCommGrpCat.{v}).map (F.map g) := by
  ext x
  exact F.map_comp f g x

/-- The underlying abelian-group-valued functor of a module-valued functor. -/
noncomputable def toFunctor (F : ModuleValuedFunctor.{u, v} A) : Under A ⥤ AddCommGrpCat.{v} where
  obj B := (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).obj (F.obj B)
  map f := (forget₂ (ModuleCat.{v} _) AddCommGrpCat.{v}).map (F.map f)
  map_id B := toFunctor_map_id F B
  map_comp f g := toFunctor_map_comp F f g

/-- Evaluating `toFunctor` returns the underlying additive group of the specified module. -/
theorem toFunctor_obj (F : ModuleValuedFunctor.{u, v} A) (B : Under A) :
    F.toFunctor.obj B =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).obj (F.obj B) := rfl

/-- A morphism of module-valued functors, with a linear component over every algebra. -/
structure Hom (F G : ModuleValuedFunctor.{u, v} A) where
  /-- The component over the algebra `B`. -/
  app (B : Under A) : F.obj B ⟶ G.obj B
  /-- The components commute with transition maps. -/
  naturality {B B' : Under A} (f : B ⟶ B') (x : F.obj B) :
    G.map f (app B x) = app B' (F.map f x)

/-- Forgetting the module structure preserves the naturality of a module-valued morphism. -/
theorem Hom.toNatTrans_naturality {F G : ModuleValuedFunctor.{u, v} A} (f : Hom F G)
    {B B' : Under A} (g : B ⟶ B') :
    F.toFunctor.map g ≫
        (forget₂ (ModuleCat.{v} B'.right) AddCommGrpCat.{v}).map (f.app B') =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (f.app B) ≫
        G.toFunctor.map g := by
  ext x
  exact (f.naturality g x).symm

/-- The underlying natural transformation of a morphism of module-valued functors. -/
def Hom.toNatTrans {F G : ModuleValuedFunctor.{u, v} A} (f : Hom F G) :
    F.toFunctor ⟶ G.toFunctor where
  app B := (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (f.app B)
  naturality B B' g := f.toNatTrans_naturality (B := B) (B' := B') g

/-- The component of the underlying natural transformation is the given linear component. -/
theorem Hom.toNatTrans_app {F G : ModuleValuedFunctor.{u, v} A} (f : Hom F G)
    (B : Under A) :
    f.toNatTrans.app B =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (f.app B) := rfl

/-- Morphisms of module-valued functors are determined by their components. -/
@[ext]
theorem hom_ext {F G : ModuleValuedFunctor.{u, v} A} {f g : Hom F G}
    (h : ∀ B, f.app B = g.app B) : f = g := by
  cases f
  cases g
  congr
  funext B
  exact h B

/-- The ring presheaf on the opposite of the category of `A`-algebras. -/
def coefficientPresheaf (A : CommRingCat.{u}) :
    (Under A)ᵒᵖᵒᵖ ⥤ RingCat.{u} :=
  (opOpEquivalence (Under A)).functor ⋙ Under.forget A ⋙
    forget₂ CommRingCat.{u} RingCat.{u}

/-- The standard module presheaf with exactly the given modules and transition maps. -/
def toPresheaf {A : CommRingCat.{u}} (F : ModuleValuedFunctor.{u, v} A) :
    PresheafOfModules.{v} (coefficientPresheaf A) where
  obj X := F.obj X.unop.unop
  map f := F.map f.unop.unop
  map_id X := by
    ext x
    exact F.map_id X.unop.unop x
  map_comp f g := by
    ext x
    exact F.map_comp f.unop.unop g.unop.unop x

/-- Recover a module-valued functor from the standard module presheaf. -/
def ofPresheaf {A : CommRingCat.{u}}
    (F : PresheafOfModules.{v} (coefficientPresheaf A)) : ModuleValuedFunctor.{u, v} A where
  obj B := F.obj (op (op B))
  map f := F.map f.op.op
  map_id B x := by
    change F.map (𝟙 (op (op B))) x = x
    rw [F.map_id]
    rfl
  map_comp f g x := F.map_comp_apply f.op.op g.op.op x

/-- The data-preserving equivalence with the standard module-presheaf model. -/
def presheafObjectEquiv (A : CommRingCat.{u}) :
    ModuleValuedFunctor.{u, v} A ≃ PresheafOfModules.{v} (coefficientPresheaf A) where
  toFun := toPresheaf
  invFun := ofPresheaf
  left_inv F := by cases F; rfl
  right_inv F := by cases F; rfl

/-- The equivalence on morphisms that preserves each linear component. -/
def presheafHomEquiv {A : CommRingCat.{u}} (F G : ModuleValuedFunctor.{u, v} A) :
    ModuleValuedFunctor.Hom F G ≃ (toPresheaf F ⟶ toPresheaf G) where
  toFun f :=
    { app := fun X ↦ f.app X.unop.unop
      naturality := fun g ↦ by
        ext x
        exact (f.naturality g.unop.unop x).symm }
  invFun f :=
    { app := fun B ↦ f.app (op (op B))
      naturality := fun g x ↦ (PresheafOfModules.naturality_apply f g.op.op x).symm }
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- Conversion to the standard model preserves the module over each algebra. -/
@[simp] theorem toPresheaf_obj (F : ModuleValuedFunctor.{u, v} A) (B : Under A) :
    F.toPresheaf.obj (op (op B)) = F.obj B := rfl

/-- Conversion to the standard model preserves each transition map. -/
@[simp] theorem toPresheaf_map (F : ModuleValuedFunctor.{u, v} A) {B B' : Under A}
    (f : B ⟶ B') : F.toPresheaf.map f.op.op = F.map f := rfl

/-- Conversion of morphisms preserves the specified linear component. -/
@[simp] theorem presheafHomEquiv_app {F G : ModuleValuedFunctor.{u, v} A}
    (f : Hom F G) (B : Under A) :
    (presheafHomEquiv F G f).app (op (op B)) = f.app B := rfl

end ModuleValuedFunctor
