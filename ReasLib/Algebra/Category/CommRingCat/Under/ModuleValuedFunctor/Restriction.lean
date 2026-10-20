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
  map_id := sorry
  map_comp := sorry

/-- Restriction preserves the module assigned to a finitely presented algebra. -/
theorem Restricted.ofGlobal_obj {A : CommRingCat.{u}} (F : ModuleValuedFunctor.{u, u} A)
    (B : FinitelyPresentedAlgebra A) : (Restricted.ofGlobal F).obj B = F.obj B.obj := sorry

namespace Restricted

/-- A morphism between module-valued functors on finitely presented algebras. -/
structure Hom {A : CommRingCat.{u}} (F G : Restricted A) where
  /-- The linear component over a finitely presented algebra. -/
  app (B : FinitelyPresentedAlgebra A) : F.obj B ⟶ G.obj B
  /-- The components commute with maps between finitely presented algebras. -/
  naturality {B B' : FinitelyPresentedAlgebra A} (f : B ⟶ B') (x : F.obj B) :
    G.map f (app B x) = app B' (F.map f x)

/-- The identity morphism of a restricted module-valued functor. -/
def Hom.id {A : CommRingCat.{u}} (F : Restricted A) : Hom F F where
  app := fun _ ↦ 𝟙 _
  naturality := sorry

/-- The identity restricted morphism acts identically on every component. -/
theorem Hom.id_app {A : CommRingCat.{u}} (F : Restricted A)
    (B : FinitelyPresentedAlgebra A) : (Hom.id F).app B = 𝟙 _ := sorry

/-- Compose morphisms of restricted module-valued functors. -/
def Hom.comp {A : CommRingCat.{u}} {F G H : Restricted A}
    (f : Hom F G) (g : Hom G H) : Hom F H where
  app B := f.app B ≫ g.app B
  naturality := sorry

/-- Composition of restricted morphisms is computed componentwise. -/
theorem Hom.comp_app {A : CommRingCat.{u}} {F G H : Restricted A}
    (f : Hom F G) (g : Hom G H) (B : FinitelyPresentedAlgebra A) :
    (Hom.comp f g).app B = f.app B ≫ g.app B := sorry

/-- Restrict a morphism of global module-valued functors. -/
def Hom.ofGlobal {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}
    (f : ModuleValuedFunctor.Hom F G) : Hom (Restricted.ofGlobal F) (Restricted.ofGlobal G) where
  app B := f.app B.obj
  naturality := sorry

/-- Restriction preserves every component of a global morphism. -/
theorem Hom.ofGlobal_app {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}
    (f : ModuleValuedFunctor.Hom F G) (B : FinitelyPresentedAlgebra A) :
    (Hom.ofGlobal f).app B = f.app B.obj := sorry

/-- The bundled category of module-valued functors on finitely presented `A`-algebras. -/
def category (A : CommRingCat.{u}) : Cat.{u + 1, u + 1} where
  α := Restricted A
  str :=
    { Hom := Hom
      id := Hom.id
      comp := Hom.comp
      id_comp := sorry
      comp_id := sorry
      assoc := sorry }

/-- Morphisms in `Restricted.category A` are componentwise-linear restricted morphisms. -/
theorem category_hom (A : CommRingCat.{u}) (F G : category A) :
    (F ⟶ G) = Hom F G := sorry

end Restricted

/-- The category of tensor-adequate module-valued functors on all `A`-algebras. -/
abbrev TensorAdeq (A : CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory (TensorAdequate (A := A))

/-- Every object of `TensorAdeq A` is tensor-adequate. -/
theorem TensorAdeq.adequate {A : CommRingCat.{u}} (F : TensorAdeq A) :
    TensorAdequate F.obj := sorry

/-- Restriction from tensor-adequate module-valued functors to finitely presented algebras. -/
def restriction (A : CommRingCat.{u}) : TensorAdeq A ⥤ Restricted.category A where
  obj F := Restricted.ofGlobal F.obj
  map f := Restricted.Hom.ofGlobal f.hom
  map_id := sorry
  map_comp := sorry

/-- The restriction functor has the expected object map. -/
theorem restriction_obj (A : CommRingCat.{u}) (F : TensorAdeq A) :
    (restriction A).obj F = Restricted.ofGlobal F.obj := sorry

/-- Restriction of tensor-adequate functors is full. -/
instance restrictionFull (A : CommRingCat.{u}) : (restriction A).Full := sorry

/-- Restriction of tensor-adequate functors is faithful. -/
instance restrictionFaithful (A : CommRingCat.{u}) : (restriction A).Faithful := sorry

/-- A tensor-adequate module-valued functor is determined by its restriction to finitely
presented algebras, on both objects and morphisms. -/
theorem restrictionFullyFaithful (A : CommRingCat.{u}) :
    Nonempty (restriction A).FullyFaithful := sorry

end ModuleValuedFunctor
