/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.CategoryTheory.Fibered.Fiber.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# The category of degree `d` finite Hilbert lifts

Objects of `H_d(X/Y)` are quintuples `(U, Z, y, x, α)` with `Z ⟶ U` finite locally
free of rank `d`, `y` in the fibre of `Y` over `U`, `x` in the fibre of `X` over
`Z`, and `α : y|_Z ≅ F(x)`. Morphisms are tuples `(f, g, b, a)` for which
`Z ≅ Z' ×_{U'} U` and the evident square of restrictions commutes. The forgetful
functor `p` sends a quintuple to `U`.
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
variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳]

/-- Restriction of a fibre object along a morphism of `S`-schemes, obtained from a
chosen cartesian lift. -/
def restrictObj {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) (f : Z ⟶ U) : p.Fiber Z :=
  Fiber.mk (IsPreFibered.pullbackObj_proj ξ.property f)

/-- The underlying total object of `restrictObj` is the chosen cartesian pullback. -/
theorem restrictObj_val {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) (f : Z ⟶ U) :
    (restrictObj ξ f).1 = IsPreFibered.pullbackObj ξ.property f := sorry

/-- Restriction along equal base morphisms yields equal fibre objects. -/
def restrictObj_eq {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) {f g : Z ⟶ U} (h : f = g) :
    restrictObj ξ f ≅ restrictObj ξ g :=
  eqToIso (congrArg (restrictObj ξ) h)

/-- The unique comparison induced by a cartesian lift, with explicit certificates. -/
def cartesianMap {p : 𝒳 ⥤ Over S} {R T : Over S} {a b a' : 𝒳}
    (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsCartesian f φ)
    (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') : a' ⟶ a :=
  @IsCartesian.map (Over S) 𝒳 _ _ p R T a b f φ hφ a' φ' hφ'

/-- The comparison `cartesianMap` is vertical over the identity of the domain. -/
theorem cartesianMap_isHomLift {p : 𝒳 ⥤ Over S} {R T : Over S} {a b a' : 𝒳}
    (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsCartesian f φ)
    (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') :
    p.IsHomLift (𝟙 R) (cartesianMap f φ hφ φ' hφ') :=
  @IsCartesian.map_isHomLift (Over S) 𝒳 _ _ p R T a b f φ hφ a' φ' hφ'

/-- A fibre morphism over `U` restricts along `f : Z ⟶ U` by the universal property
of the chosen cartesian lift. -/
def restrictHom {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    {ξ ξ' : p.Fiber U} (φ : ξ ⟶ ξ') (f : Z ⟶ U) :
    restrictObj ξ f ⟶ restrictObj ξ' f :=
  let φX := IsPreFibered.pullbackMap ξ.property f
  let φY := IsPreFibered.pullbackMap ξ'.property f
  let φ' := φX ≫ φ.1
  let hφ' : p.IsHomLift f φ' :=
    @IsHomLift.comp_lift_id_right _ _ _ _ p _ _ _ _ _ f φX
      (IsPreFibered.pullbackMap.IsCartesian ξ.property f).toIsHomLift φ.1 φ.2
  Fiber.Hom.mk (cartesianMap f φY (IsPreFibered.pullbackMap.IsCartesian ξ'.property f) φ' hφ')
    (cartesianMap_isHomLift f φY (IsPreFibered.pullbackMap.IsCartesian ξ'.property f) φ' hφ')

/-- Restriction of a fibre isomorphism along a morphism of `S`-schemes. -/
def restrictIso {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    {ξ ξ' : p.Fiber U} (e : ξ ≅ ξ') (f : Z ⟶ U) :
    restrictObj ξ f ≅ restrictObj ξ' f where
  hom := restrictHom e.hom f
  inv := restrictHom e.inv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction along the identity recovers the original fibre object. -/
def restrictObj_id {p : 𝒳 ⥤ Over S} [p.IsFibered] {U : Over S}
    (ξ : p.Fiber U) : restrictObj ξ (𝟙 U) ≅ ξ :=
  let φ := IsPreFibered.pullbackMap ξ.property (𝟙 U)
  let hφ := IsPreFibered.pullbackMap.IsCartesian ξ.property (𝟙 U)
  let hid : p.IsHomLift (𝟙 U) (𝟙 ξ.1) := IsHomLift.id ξ.property
  { hom := Fiber.Hom.mk φ hφ.toIsHomLift
    inv := Fiber.Hom.mk (cartesianMap (𝟙 U) φ hφ (𝟙 ξ.1) hid)
      (cartesianMap_isHomLift (𝟙 U) φ hφ (𝟙 ξ.1) hid)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Successive restrictions along `f` then `g` agree with restriction along `g ≫ f`. -/
def restrictObj_comp {p : 𝒳 ⥤ Over S} [p.IsFibered]
    {U V W : Over S} (ξ : p.Fiber U) (f : V ⟶ U) (g : W ⟶ V) :
    restrictObj (restrictObj ξ f) g ≅ restrictObj ξ (g ≫ f) :=
  let i := (IsFibered.pullbackPullbackIso ξ.property f g).symm
  { hom := Fiber.Hom.mk i.hom
      (IsCartesian.domainUniqueUpToIso_hom_isHomLift p (g ≫ f)
        (IsPreFibered.pullbackMap (IsPreFibered.pullbackObj_proj ξ.property f) g ≫
          IsPreFibered.pullbackMap ξ.property f)
        (IsPreFibered.pullbackMap ξ.property (g ≫ f)))
    inv := Fiber.Hom.mk i.inv
      (IsCartesian.domainUniqueUpToIso_inv_isHomLift p (g ≫ f)
        (IsPreFibered.pullbackMap (IsPreFibered.pullbackObj_proj ξ.property f) g ≫
          IsPreFibered.pullbackMap ξ.property f)
        (IsPreFibered.pullbackMap ξ.property (g ≫ f)))
    hom_inv_id := sorry
    inv_hom_id := sorry }

variable {X Y : GroupoidsOver S}

/-- An object of the degree `d` finite Hilbert category of a 1-morphism `F : X ⟶ Y`. -/
structure Obj (F : X ⟶ Y) (d : ℕ) where
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
    (Obj.of U Z π hπ y x iso).U = U := sorry

/-- The constructor `Obj.of` stores the supplied finite locally free scheme. -/
theorem Obj.of_Z {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).Z = Z := sorry

/-- The constructor `Obj.of` stores the supplied structure morphism. -/
theorem Obj.of_π {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).π = π := sorry

/-- The constructor `Obj.of` stores the supplied fibre object of `Y`. -/
theorem Obj.of_y {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).y = y := sorry

/-- The constructor `Obj.of` stores the supplied fibre object of `X`. -/
theorem Obj.of_x {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).x = x := sorry

/-- The constructor `Obj.of` stores the supplied isomorphism `y|_Z ≅ F(x)`. -/
theorem Obj.of_iso {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).iso = iso := sorry

/-- An object of `H_d(X/Y)` has `Z ⟶ U` finite locally free of rank `d`. -/
theorem Obj.spec {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) :
    IsFiniteLocallyFreeOfRank ξ.π.left d := sorry

/-- The two paths `α` then `F(a)` and `b|_Z` then `α'` then the cartesian lift of
`F(x')`, compared after postcomposition to `F(x')`. -/
def HomCompatible {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
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
structure Hom {F : X ⟶ Y} {d : ℕ} (ξ ξ' : Obj F d) where
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
  /-- The source square of `α`, `b|_Z`, `F(a)`, and `α'` commutes. -/
  comm : HomCompatible f g over_comm b a

/-- Assemble a morphism of `H_d(X/Y)` from `(f, g, b, a)`, the pullback square,
and the source commutativity square. -/
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
    (Hom.homMk f g hfg hpb b a hcomm).f = f := sorry

/-- The constructor `homMk` stores the supplied map of finite locally free schemes. -/
theorem Hom.homMk_g {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).g = g := sorry

/-- The constructor `homMk` stores the supplied fibre isomorphism `b`. -/
theorem Hom.homMk_b {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).b = b := sorry

/-- The constructor `homMk` stores the supplied fibre isomorphism `a`. -/
theorem Hom.homMk_a {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).a = a := sorry

/-- The constructor `homMk` stores the supplied commutativity proof. -/
theorem Hom.homMk_comm {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).comm = hcomm := sorry

/-- A morphism of `H_d(X/Y)` induces a pullback square of finite locally free
morphisms. -/
theorem Hom.spec {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d} (φ : Hom ξ ξ') :
    IsPullback φ.g.left ξ.π.left ξ'.π.left φ.f.left := sorry

/-- The identity morphism of a quintuple, using identity restrictions. -/
def idHom {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := 𝟙 ξ.Z
  over_comm := sorry
  isPullback := sorry
  b := (restrictObj_id ξ.y).symm
  a := (restrictObj_id ξ.x).symm
  comm := sorry

/-- Composite of two morphisms of quintuples. -/
def compHom {F : X ⟶ Y} {d : ℕ} {ξ ξ' ξ'' : Obj F d}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := α.g ≫ β.g
  over_comm := sorry
  isPullback := sorry
  b := α.b ≪≫ restrictIso β.b α.f ≪≫ restrictObj_comp ξ''.y β.f α.f
  a := α.a ≪≫ restrictIso β.a α.g ≪≫ restrictObj_comp ξ''.x β.g α.g
  comm := sorry

/-- Quintuples `(U, Z, y, x, α)` and morphisms `(f, g, b, a)` form a category. -/
instance category (F : X ⟶ Y) (d : ℕ) : Category (Obj F d) where
  Hom := Hom
  id := idHom
  comp := fun α β ↦ compHom α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The identity morphism of `p` is the identity of the test scheme. -/
theorem idHom_f {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) : (idHom ξ).f = 𝟙 ξ.U := sorry

/-- Composition in `H_d(X/Y)` projects to composition of test-scheme morphisms. -/
theorem compHom_f {F : X ⟶ Y} {d : ℕ} {ξ ξ' ξ'' : Obj F d}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : (compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor sending `(U, Z, y, x, α)` to `U`. -/
def p (F : X ⟶ Y) (d : ℕ) : Obj F d ⥤ Over S where
  obj ξ := ξ.U
  map φ := φ.f
  map_id := idHom_f
  map_comp := compHom_f

/-- The object part of `p` is the underlying test scheme. -/
theorem p_obj {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) : (p F d).obj ξ = ξ.U := sorry

/-- The morphism part of `p` is the underlying map of test schemes. -/
theorem p_map {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d} (φ : ξ ⟶ ξ') :
    (p F d).map φ = φ.f := sorry

/-- The forgetful functor `p : H_d(X/Y) ⟶ (Sch/S)` is fibered in groupoids. -/
instance instIsFiberedInGroupoids (F : X ⟶ Y) (d : ℕ) :
    Functor.IsFibered.InGroupoids (p F d) := sorry

end AlgebraicGeometry.FiniteHilbertStack
