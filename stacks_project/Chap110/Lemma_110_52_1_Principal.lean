module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import stacks_project.Chap78.Definition_78_9_3_Torsor
public import stacks_project.Chap95.Lemma_95_14_10_Torsors

/-!
# Principal homogeneous spaces under a group algebraic space

The stack in groupoids of principal homogeneous `G_U`-spaces for a group
algebraic space `G` over an algebraic space `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

namespace Principal

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- An object of `G`-Principal: a scheme `U` over `S`, a morphism `b : U ⟶ B`, and
a principal homogeneous `G_U`-space. -/
structure Obj (G : GroupAlgebraicSpace B) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The morphism `b : U ⟶ B` of algebraic spaces over `S`. -/
  b : ofOver U ⟶ B
  /-- The principal homogeneous `G_U`-space over `U`. -/
  X : Action (grpOverPullback G b)
  /-- The action `X` is an fpqc `G_U`-torsor in the sense of `IsTorsor`. -/
  isPrincipal : IsTorsor (grpOverPullback G b) X

variable {G : GroupAlgebraicSpace B}

/-- Assemble an object of `G`-Principal from a scheme, a morphism to `B`, and a
principal homogeneous `G_U`-space. -/
def ofTorsor (U : Over S) (b : ofOver U ⟶ B) (X : Action (grpOverPullback G b))
    (hX : IsTorsor (grpOverPullback G b) X) : Obj G where
  U := U
  b := b
  X := X
  isPrincipal := hX

/-- The constructor of `Obj` stores the supplied scheme, morphism, action, and
fpqc witness. -/
theorem ofTorsor_spec (U : Over S) (b : ofOver U ⟶ B)
    (X : Action (grpOverPullback G b))
    (hX : IsTorsor (grpOverPullback G b) X) :
    (ofTorsor U b X hX).U = U ∧ (ofTorsor U b X hX).b = b ∧
      (ofTorsor U b X hX).X = X ∧ (ofTorsor U b X hX).isPrincipal = hX := sorry

/-- Comparison of group objects `G_U` and the pullback of `G_{U'}` along `f`. -/
def groupCompare {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b) :
    (grpOverPullback G ξ.b).X ⟶
      ((overPullback (ofOverMap f)).mapGrp.obj (grpOverPullback G ξ'.b)).X :=
  eqToHom (congrArg (fun t ↦ (overPullback t).obj G.X) h) ≫
    (overPullbackCompIso ξ'.b (ofOverMap f) G.X).hom

/-- An isomorphism of underlying objects over `U` is `G_U`-equivariant when it
intertwines the action morphisms after identifying the pulled-back group. -/
def IsEquivariant {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (overPullback (ofOverMap f)).obj ξ'.X.X) : Prop :=
  ξ.X.mod.smul ≫ g.hom =
    (groupCompare f h ⊗ₘ g.hom) ≫
      (pullbackAction (ofOverMap f) (grpOverPullback G ξ'.b) ξ'.X).mod.smul

/-- A morphism of `G`-Principal: a map of schemes over `B` and an equivariant
isomorphism of principal homogeneous `G_U`-spaces. -/
structure Hom {G : GroupAlgebraicSpace B} (ξ ξ' : Obj G) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism `f` lies over `B`. -/
  comm : ξ.b = ofOverMap f ≫ ξ'.b
  /-- The isomorphism of underlying objects after pullback along `f`. -/
  g : ξ.X.X ≅ (overPullback (ofOverMap f)).obj ξ'.X.X
  /-- The isomorphism `g` is `G_U`-equivariant. -/
  equivariant : IsEquivariant f comm g

/-- Assemble a morphism of `G`-Principal from a scheme map and an equivariant
isomorphism of principal homogeneous spaces. -/
def ofIso {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U) (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (overPullback (ofOverMap f)).obj ξ'.X.X)
    (hg : IsEquivariant f h g) : Hom ξ ξ' where
  f := f
  comm := h
  g := g
  equivariant := hg

/-- The constructor of `Hom` stores the supplied scheme map, over-`B` equality,
isomorphism, and equivariance witness. -/
theorem ofIso_spec {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (overPullback (ofOverMap f)).obj ξ'.X.X)
    (hg : IsEquivariant f h g) :
    (ofIso f h g hg).f = f ∧ (ofIso f h g hg).comm = h ∧
      (ofIso f h g hg).g = g ∧ (ofIso f h g hg).equivariant = hg := sorry

/-- Identity of schemes over `S` is compatible with the morphism to `B`. -/
theorem id_comm (ξ : Obj G) : ξ.b = ofOverMap (𝟙 ξ.U) ≫ ξ.b := sorry

/-- The identity comparison of slice objects along `id`. -/
def idIso (ξ : Obj G) :
    ξ.X.X ≅ (overPullback (ofOverMap (𝟙 ξ.U))).obj ξ.X.X :=
  pullbackAlongIdIso ξ.X.X ≪≫
    eqToIso (congrArg (fun t ↦ (overPullback t).obj ξ.X.X) (ofOverMap_id ξ.U).symm)

/-- The identity comparison of principal homogeneous spaces is equivariant. -/
theorem id_equivariant (ξ : Obj G) :
    IsEquivariant (𝟙 ξ.U) (id_comm ξ) (idIso ξ) := sorry

/-- Identity morphisms of `G`-Principal. -/
def idHom (ξ : Obj G) : Hom ξ ξ where
  f := 𝟙 ξ.U
  comm := id_comm ξ
  g := idIso ξ
  equivariant := id_equivariant ξ

/-- The composite isomorphism of underlying objects along a composite of scheme maps. -/
def compIso {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.X.X ≅ (overPullback (ofOverMap (α.f ≫ β.f))).obj ξ''.X.X :=
  α.g ≪≫ (overPullback (ofOverMap α.f)).mapIso β.g ≪≫
    (overPullbackCompIso (ofOverMap β.f) (ofOverMap α.f) ξ''.X.X).symm ≪≫
      eqToIso (congrArg (fun t ↦ (overPullback t).obj ξ''.X.X) (ofOverMap_comp α.f β.f).symm)

/-- Compatibility of a composite morphism with the maps to `B`. -/
theorem comp_comm {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.b = ofOverMap (α.f ≫ β.f) ≫ ξ''.b := sorry

/-- The composite isomorphism of principal homogeneous spaces is equivariant. -/
theorem comp_equivariant {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariant (α.f ≫ β.f) (comp_comm α β) (compIso α β) := sorry

/-- Composition of morphisms of `G`-Principal. -/
def compHom {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  comm := comp_comm α β
  g := compIso α β
  equivariant := comp_equivariant α β

/-- Left identity law for morphisms of `G`-Principal. -/
theorem idHom_comp {ξ ξ' : Obj G} (α : Hom ξ ξ') : compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `G`-Principal. -/
theorem compHom_id {ξ ξ' : Obj G} (α : Hom ξ ξ') : compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `G`-Principal. -/
theorem assocHom {ξ₁ ξ₂ ξ₃ ξ₄ : Obj G} (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (c : Hom ξ₃ ξ₄) :
    compHom (compHom α β) c = compHom α (compHom β c) := sorry

/-- The category of objects of `G`-Principal. -/
instance instCategory : Category (Obj G) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom ξ
  comp α β := compHom α β
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id (ξ : Obj G) : (idHom ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor from `G`-Principal to `(Sch/S)_fppf`. -/
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

/-- The stack in groupoids of principal homogeneous `G`-spaces over `(Sch/S)_fppf`. -/
def stack (G : GroupAlgebraicSpace B) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget G)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (G : GroupAlgebraicSpace B) : (stack G).p = forget G := sorry

end Principal

end AlgebraicGeometry.GroupAlgebraicSpace
