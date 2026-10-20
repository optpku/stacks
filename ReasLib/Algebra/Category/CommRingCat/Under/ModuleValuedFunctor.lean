module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Constructions

@[expose] public section

open CategoryTheory

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
      𝟙 ((forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).obj (F.obj B)) := sorry

/-- Forgetting the module structure preserves composition of transition maps. -/
theorem toFunctor_map_comp (F : ModuleValuedFunctor.{u, v} A) {B B' B'' : Under A}
    (f : B ⟶ B') (g : B' ⟶ B'') :
    (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (F.map (f ≫ g)) =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (F.map f) ≫
        (forget₂ (ModuleCat.{v} B'.right) AddCommGrpCat.{v}).map (F.map g) := sorry

/-- The underlying abelian-group-valued functor of a module-valued functor. -/
noncomputable def toFunctor (F : ModuleValuedFunctor.{u, v} A) : Under A ⥤ AddCommGrpCat.{v} where
  obj B := (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).obj (F.obj B)
  map f := (forget₂ (ModuleCat.{v} _) AddCommGrpCat.{v}).map (F.map f)
  map_id B := toFunctor_map_id F B
  map_comp f g := toFunctor_map_comp F f g

/-- Evaluating `toFunctor` returns the underlying additive group of the specified module. -/
theorem toFunctor_obj (F : ModuleValuedFunctor.{u, v} A) (B : Under A) :
    F.toFunctor.obj B =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).obj (F.obj B) := sorry

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
        G.toFunctor.map g := sorry

/-- The underlying natural transformation of a morphism of module-valued functors. -/
def Hom.toNatTrans {F G : ModuleValuedFunctor.{u, v} A} (f : Hom F G) :
    F.toFunctor ⟶ G.toFunctor where
  app B := (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (f.app B)
  naturality B B' g := f.toNatTrans_naturality (B := B) (B' := B') g

/-- The component of the underlying natural transformation is the given linear component. -/
theorem Hom.toNatTrans_app {F G : ModuleValuedFunctor.{u, v} A} (f : Hom F G)
    (B : Under A) :
    f.toNatTrans.app B =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (f.app B) := sorry

end ModuleValuedFunctor
