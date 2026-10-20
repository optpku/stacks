/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The category of finite Hilbert lifts

Objects are quintuples `(U, Z, y, x, α)` with `Z ⟶ U` finite locally free
of the specified rank and `α : y|_Z ≅ F(x)`. Morphisms preserve these data
and give pullback squares on the finite locally free schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S}

/-- An object of the degree `d` finite Hilbert category of a 1-morphism `F : X ⟶ Y`. -/
structure Object (F : X ⟶ Y) (d : ℕ) where
  /-- The test scheme over `S`. -/
  U : Over S
  /-- The finite locally free scheme over `U`. -/
  Z : Over S
  /-- The structure morphism `Z ⟶ U`. -/
  π : Z ⟶ U
  /-- `π` is finite locally free of rank `d`. -/
  finiteLocallyFree : IsFiniteLocallyFreeOfRank π.left d
  /-- The fibre object of `Y` over `U`. -/
  y : Y.p.Fiber U
  /-- The fibre object of `X` over `Z`. -/
  x : X.p.Fiber Z
  /-- The isomorphism `y|_Z ≅ F(x)`. -/
  iso : restrictObj y π ≅ (fiberFunctor F Z).obj x

/-- The two paths `α` then `F(a)` and `b|_Z` then `α'` then the cartesian lift of
`F(x')`, compared after postcomposition to `F(x')`. -/
def HomCompatible {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Object F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g) : Prop :=
  ξ.iso.hom.1 ≫ ((fiberFunctor F ξ.Z).map a.hom).1 ≫
      (toFunctor F).map (IsPreFibered.pullbackMap ξ'.x.property g) =
    (restrictHom b.hom ξ.π).1 ≫ (restrictObj_comp ξ'.y f ξ.π).hom.1 ≫
      (restrictObj_eq ξ'.y hfg).hom.1 ≫ (restrictObj_comp ξ'.y ξ'.π g).inv.1 ≫
        (restrictHom ξ'.iso.hom g).1 ≫
          IsPreFibered.pullbackMap ((fiberFunctor F ξ'.Z).obj ξ'.x).property g

/-- A morphism of quintuples is given by `(f, g, b, a)` with a pullback square on
the finite locally free morphisms. -/
structure Hom {F : X ⟶ Y} {d : ℕ} (ξ ξ' : Object F d) where
  /-- The underlying morphism of test schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism of finite locally free schemes. -/
  g : ξ.Z ⟶ ξ'.Z
  /-- The square of structure morphisms commutes in `(Sch/S)`. -/
  over_comm : ξ.π ≫ f = g ≫ ξ'.π
  /-- `g` realises `Z` as the base change `Z' ×_{U'} U`. -/
  isPullback : IsPullback g.left ξ.π.left ξ'.π.left f.left
  /-- The fibre isomorphism `y ≅ f^* y'`. -/
  b : ξ.y ≅ restrictObj ξ'.y f
  /-- The fibre isomorphism `x ≅ g^* x'`. -/
  a : ξ.x ≅ restrictObj ξ'.x g
  /-- The square of `α`, `b|_Z`, `F(a)`, and `α'` commutes. -/
  comm : HomCompatible f g over_comm b a

/-- The identity morphism of a quintuple, using identity restrictions. -/
def idHom {F : X ⟶ Y} {d : ℕ} (ξ : Object F d) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := 𝟙 ξ.Z
  over_comm := sorry
  isPullback := sorry
  b := (restrictObj_id ξ.y).symm
  a := (restrictObj_id ξ.x).symm
  comm := sorry

/-- Composite of two morphisms of quintuples. -/
def compHom {F : X ⟶ Y} {d : ℕ} {ξ ξ' ξ'' : Object F d}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := α.g ≫ β.g
  over_comm := sorry
  isPullback := sorry
  b := α.b ≪≫ restrictIso β.b α.f ≪≫ restrictObj_comp ξ''.y β.f α.f
  a := α.a ≪≫ restrictIso β.a α.g ≪≫ restrictObj_comp ξ''.x β.g α.g
  comm := sorry

/-- Quintuples with finite locally free structure maps of rank `d`, together with
pullback-compatible morphisms, form a bundled category. -/
def category (F : X ⟶ Y) (d : ℕ) : Cat.{u, u + 1} :=
  ⟨Object F d, {
    Hom := Hom
    id := idHom
    comp := fun α β ↦ compHom α β
    id_comp := sorry
    comp_id := sorry
    assoc := sorry }⟩

/-- The carrier of the category of finite locally free degree-`d` lifts along `F`. -/
abbrev Obj (F : X ⟶ Y) (d : ℕ) : Type (u + 1) := category F d

/-- Package a quintuple `(U, Z, y, x, α)` as an object of `H_d(X/Y)`. -/
def Obj.of {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) : Obj F d where
  U := U
  Z := Z
  π := π
  finiteLocallyFree := hπ
  y := y
  x := x
  iso := iso

/-- The constructor `Obj.of` stores the supplied test scheme. -/
theorem Obj.of_U {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).U = U := rfl

/-- The constructor `Obj.of` stores the supplied finite locally free scheme. -/
theorem Obj.of_Z {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).Z = Z := rfl

/-- The constructor `Obj.of` stores the supplied structure morphism. -/
theorem Obj.of_π {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).π = π := rfl

/-- The constructor `Obj.of` stores the supplied fibre object of `Y`. -/
theorem Obj.of_y {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).y = y := rfl

/-- The constructor `Obj.of` stores the supplied fibre object of `X`. -/
theorem Obj.of_x {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).x = x := rfl

/-- The constructor `Obj.of` stores the supplied isomorphism `y|_Z ≅ F(x)`. -/
theorem Obj.of_iso {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).iso = iso := rfl

/-- An object of `H_d(X/Y)` has `Z ⟶ U` finite locally free of rank `d`. -/
theorem Obj.spec {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) :
    IsFiniteLocallyFreeOfRank ξ.π.left d := ξ.finiteLocallyFree

/-- Assemble a morphism of `H_d(X/Y)` from `(f, g, b, a)`, the pullback square,
and the commutativity square. -/
def Hom.homMk {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    Hom ξ ξ' where
  f := f
  g := g
  over_comm := hfg
  isPullback := hpb
  b := b
  a := a
  comm := hcomm

/-- The constructor `homMk` stores the supplied map of test schemes. -/
theorem Hom.homMk_f {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).f = f := rfl

/-- The constructor `homMk` stores the supplied map of finite locally free schemes. -/
theorem Hom.homMk_g {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).g = g := rfl

/-- The constructor `homMk` stores the supplied fibre isomorphism `b`. -/
theorem Hom.homMk_b {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).b = b := rfl

/-- The constructor `homMk` stores the supplied fibre isomorphism `a`. -/
theorem Hom.homMk_a {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).a = a := rfl

/-- The constructor `homMk` stores the supplied commutativity proof. -/
theorem Hom.homMk_comm {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).comm = hcomm := rfl

/-- A morphism of `H_d(X/Y)` induces a pullback square of finite locally free
morphisms. -/
theorem Hom.spec {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d} (φ : Hom ξ ξ') :
    IsPullback φ.g.left ξ.π.left ξ'.π.left φ.f.left := φ.isPullback

/-- The identity morphism of `p` is the identity of the test scheme. -/
theorem idHom_f {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) : (idHom ξ).f = 𝟙 ξ.U := rfl

/-- Composition in `H_d(X/Y)` projects to composition of test-scheme morphisms. -/
theorem compHom_f {F : X ⟶ Y} {d : ℕ} {ξ ξ' ξ'' : Obj F d}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : (compHom α β).f = α.f ≫ β.f := rfl

/-- The forgetful functor sending `(U, Z, y, x, α)` to `U`. -/
def p (F : X ⟶ Y) (d : ℕ) : Obj F d ⥤ Over S where
  obj ξ := ξ.U
  map φ := φ.f
  map_id := idHom_f
  map_comp := compHom_f

/-- The object part of `p` is the underlying test scheme. -/
theorem p_obj {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) : (p F d).obj ξ = ξ.U := rfl

/-- The morphism part of `p` is the underlying map of test schemes. -/
theorem p_map {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d} (φ : ξ ⟶ ξ') :
    (p F d).map φ = φ.f := rfl

/-- The forgetful functor `p : H_d(X/Y) ⟶ (Sch/S)` is fibered in groupoids. -/
instance instIsFiberedInGroupoids (F : X ⟶ Y) (d : ℕ) :
    Functor.IsFibered.InGroupoids (p F d) := sorry

end AlgebraicGeometry.FiniteHilbertStack
