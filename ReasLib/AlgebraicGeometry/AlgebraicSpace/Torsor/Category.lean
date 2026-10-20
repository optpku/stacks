module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor

/-!
# The category and stack of algebraic-space torsors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Torsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- An object of `G`-Torsors: a scheme `U` over `S`, a morphism `b : U ⟶ B`, and
an fppf `G_U`-torsor. -/
structure Object (G : GroupAlgebraicSpace B) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The morphism `b : U ⟶ B` of algebraic spaces over `S`. -/
  b : ofOver U ⟶ B
  /-- The fppf `G_U`-torsor over `U`. -/
  X : Action (baseChange G b)
  /-- The action `X` is an fppf `G_U`-torsor in the sense of
  `IsStandardTorsor`. -/
  isTorsor : IsStandardTorsor (baseChange G b) X .fppf

variable {G : GroupAlgebraicSpace B}

/-- Assemble an object of `G`-Torsors from a scheme, a morphism to `B`, and an
fppf torsor. -/
def ofTorsor (U : Over S) (b : ofOver U ⟶ B) (X : Action (baseChange G b))
    (hX : IsStandardTorsor (baseChange G b) X .fppf) : Object G where
  U := U
  b := b
  X := X
  isTorsor := hX

/-- The constructor of `Object` stores the supplied scheme, morphism, torsor, and
fppf witness. -/
theorem ofTorsor_spec (U : Over S) (b : ofOver U ⟶ B)
    (X : Action (baseChange G b))
    (hX : IsStandardTorsor (baseChange G b) X .fppf) :
    (ofTorsor U b X hX).U = U ∧ (ofTorsor U b X hX).b = b ∧
      (ofTorsor U b X hX).X = X ∧ (ofTorsor U b X hX).isTorsor = hX := sorry

/-- Comparison of group objects `G_U` and the pullback of `G_{U'}` along `f`. -/
def groupCompare {ξ ξ' : Object G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b) :
    (baseChange G ξ.b).X ⟶
      ((Over.pullback (ofOverMap f)).mapGrp.obj (baseChange G ξ'.b)).X :=
  eqToHom (congrArg (fun t ↦ (Over.pullback t).obj G.X) h) ≫
    ((Over.pullbackComp (ofOverMap f) ξ'.b).app G.X).hom

/-- An isomorphism of underlying objects over `U` is `G_U`-equivariant when it
intertwines the action morphisms after identifying the pulled-back group. -/
def IsEquivariant {ξ ξ' : Object G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (Over.pullback (ofOverMap f)).obj ξ'.X.X) : Prop :=
  ξ.X.mod.smul ≫ g.hom =
    (groupCompare f h ⊗ₘ g.hom) ≫ (pullbackAction (ofOverMap f) (baseChange G ξ'.b) ξ'.X).mod.smul

/-- A morphism of `G`-Torsors: a map of schemes over `B` and an equivariant
isomorphism of `G_U`-torsors. -/
structure Hom {G : GroupAlgebraicSpace B} (ξ ξ' : Object G) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism `f` lies over `B`. -/
  comm : ξ.b = ofOverMap f ≫ ξ'.b
  /-- The isomorphism of underlying objects after pullback along `f`. -/
  g : ξ.X.X ≅ (Over.pullback (ofOverMap f)).obj ξ'.X.X
  /-- The isomorphism `g` is `G_U`-equivariant. -/
  equivariant : IsEquivariant f comm g

/-- Assemble a morphism of `G`-Torsors from a scheme map and an equivariant
isomorphism of torsors. -/
def ofIso {ξ ξ' : Object G} (f : ξ.U ⟶ ξ'.U) (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (Over.pullback (ofOverMap f)).obj ξ'.X.X)
    (hg : IsEquivariant f h g) : Hom ξ ξ' where
  f := f
  comm := h
  g := g
  equivariant := hg

/-- The constructor of `Hom` stores the supplied scheme map, over-`B` equality,
isomorphism, and equivariance witness. -/
theorem ofIso_spec {ξ ξ' : Object G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (Over.pullback (ofOverMap f)).obj ξ'.X.X)
    (hg : IsEquivariant f h g) :
    (ofIso f h g hg).f = f ∧ (ofIso f h g hg).comm = h ∧
      (ofIso f h g hg).g = g ∧ (ofIso f h g hg).equivariant = hg := sorry

/-- Identity of schemes over `S` is compatible with the morphism to `B`. -/
theorem id_comm (ξ : Object G) : ξ.b = ofOverMap (𝟙 ξ.U) ≫ ξ.b := sorry

/-- The identity comparison of slice objects along `id`. -/
def idIso (ξ : Object G) :
    ξ.X.X ≅ (Over.pullback (ofOverMap (𝟙 ξ.U))).obj ξ.X.X :=
  (Over.pullbackId.app ξ.X.X).symm ≪≫
    eqToIso (congrArg (fun t ↦ (Over.pullback t).obj ξ.X.X) (ofOverMap_id ξ.U).symm)

/-- The identity comparison of torsors is equivariant. -/
theorem id_equivariant (ξ : Object G) :
    IsEquivariant (𝟙 ξ.U) (id_comm ξ) (idIso ξ) := sorry

/-- Identity morphisms of `G`-Torsors. -/
def idHom (ξ : Object G) : Hom ξ ξ where
  f := 𝟙 ξ.U
  comm := id_comm ξ
  g := idIso ξ
  equivariant := id_equivariant ξ

/-- The composite isomorphism of underlying objects along a composite of scheme maps. -/
def compIso {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.X.X ≅ (Over.pullback (ofOverMap (α.f ≫ β.f))).obj ξ''.X.X :=
  α.g ≪≫ (Over.pullback (ofOverMap α.f)).mapIso β.g ≪≫
    ((Over.pullbackComp (ofOverMap α.f) (ofOverMap β.f)).app ξ''.X.X).symm ≪≫
      eqToIso (congrArg (fun t ↦ (Over.pullback t).obj ξ''.X.X) (ofOverMap_comp α.f β.f).symm)

/-- Compatibility of a composite morphism with the maps to `B`. -/
theorem comp_comm {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.b = ofOverMap (α.f ≫ β.f) ≫ ξ''.b := sorry

/-- The composite isomorphism of torsors is equivariant. -/
theorem comp_equivariant {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariant (α.f ≫ β.f) (comp_comm α β) (compIso α β) := sorry

/-- Composition of morphisms of `G`-Torsors. -/
def compHom {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  comm := comp_comm α β
  g := compIso α β
  equivariant := comp_equivariant α β

/-- Left identity law for morphisms of `G`-Torsors. -/
theorem idHom_comp {ξ ξ' : Object G} (α : Hom ξ ξ') : compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `G`-Torsors. -/
theorem compHom_id {ξ ξ' : Object G} (α : Hom ξ ξ') : compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `G`-Torsors. -/
theorem assocHom {ξ₁ ξ₂ ξ₃ ξ₄ : Object G} (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (c : Hom ξ₃ ξ₄) :
    compHom (compHom α β) c = compHom α (compHom β c) := sorry

/-- The category of objects of `G`-Torsors. -/
@[reducible]
def category (G : GroupAlgebraicSpace B) : Category (Object G) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom ξ
  comp α β := compHom α β
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- The bundled category of relative torsor triples. -/
def cat (G : GroupAlgebraicSpace B) : Cat :=
  ⟨Object G, category G⟩

/-- The objects of the bundled category of relative torsors. -/
abbrev Obj (G : GroupAlgebraicSpace B) : Type (u + 1) := cat G

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id (ξ : Obj G) : (idHom ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor from `G`-Torsors to `(Sch/S)_fppf`. -/
def forget (G : GroupAlgebraicSpace B) : Obj G ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, b, X)` to `U`. -/
theorem forget_obj (ξ : Obj G) : (forget G).obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ξ ξ' : Obj G} (α : Hom ξ ξ') : (forget G).map α = α.f := sorry

/-- The forgetful functor is fibered in groupoids. -/
instance instIsFiberedInGroupoids : Functor.IsFibered.InGroupoids (forget G) := sorry

/-- The forgetful functor is a stack in groupoids on the big fppf site. -/
instance instIsStackInGroupoids :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G) := sorry

/-- The stack in groupoids of fppf `G`-torsors over `(Sch/S)_fppf`. -/
def stack (G : GroupAlgebraicSpace B) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget G)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p : (stack G).p = forget G := sorry

/-- Each fiber of the relative fppf torsor projection is essentially small in
the universe of the base scheme. -/
instance fibers_essentiallySmall (G : GroupAlgebraicSpace B) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget G).Fiber U)) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Torsors
