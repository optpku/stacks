module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import stacks_project.Chap95.Lemma_95_14_10_Torsors

/-!
# Quotient stack of a group algebraic space action

This module records the stack in groupoids `[[X/G]]` attached to an action of a
group algebraic space `G` over `B` on an algebraic space `X` over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupAlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.QuotientStack.GroupAction

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A map of `G_U`-actions is equivariant when it intertwines the action morphisms. -/
def IsEquivariantMap {G : GroupAlgebraicSpace B} {X : Action G}
    {U : Over S} {b : ofOver U ⟶ B} (P : Action (grpOverPullback G b))
    (φ : P.X ⟶ (pullbackAction b G X).X) : Prop :=
  P.mod.smul ≫ φ =
    ((grpOverPullback G b).X ⊴ₗ φ) ≫ (pullbackAction b G X).mod.smul

/-- Equivariance of a map of `G_U`-actions is the intertwining identity for `smul`. -/
theorem isEquivariantMap_iff {G : GroupAlgebraicSpace B} {X : Action G}
    {U : Over S} {b : ofOver U ⟶ B} (P : Action (grpOverPullback G b))
    (φ : P.X ⟶ (pullbackAction b G X).X) :
    IsEquivariantMap P φ ↔
      P.mod.smul ≫ φ =
        ((grpOverPullback G b).X ⊴ₗ φ) ≫ (pullbackAction b G X).mod.smul := sorry

/-- An object of `[[X/G]]`: a scheme `U` over `S`, a morphism `b : U ⟶ B`, an
fppf `G_U`-torsor, and a `G_U`-equivariant map to the base change of `X`. -/
structure Obj (G : GroupAlgebraicSpace B) (X : Action G) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The morphism `b : U ⟶ B` of algebraic spaces over `S`. -/
  b : ofOver U ⟶ B
  /-- The fppf `G_U`-torsor over `U`. -/
  P : Action (grpOverPullback G b)
  /-- The action `P` is an fppf `G_U`-torsor. -/
  isTorsor : IsStandardTorsor (grpOverPullback G b) P .fppf
  /-- The `G_U`-equivariant map `φ : P ⟶ X ×_{B, b} U`. -/
  φ : P.X ⟶ (pullbackAction b G X).X
  /-- The map `φ` is a morphism of `G_U`-actions. -/
  equivariant : IsEquivariantMap P φ

variable {G : GroupAlgebraicSpace B} {X : Action G}

/-- Assemble an object of `[[X/G]]` from a torsor and an equivariant map. -/
def ofTorsor (U : Over S) (b : ofOver U ⟶ B) (P : Action (grpOverPullback G b))
    (hP : IsStandardTorsor (grpOverPullback G b) P .fppf)
    (φ : P.X ⟶ (pullbackAction b G X).X) (hφ : IsEquivariantMap P φ) : Obj G X where
  U := U
  b := b
  P := P
  isTorsor := hP
  φ := φ
  equivariant := hφ

/-- The constructor of `Obj` stores the supplied scheme, morphism, torsor, map,
and equivariance witness. -/
theorem ofTorsor_spec (U : Over S) (b : ofOver U ⟶ B)
    (P : Action (grpOverPullback G b))
    (hP : IsStandardTorsor (grpOverPullback G b) P .fppf)
    (φ : P.X ⟶ (pullbackAction b G X).X) (hφ : IsEquivariantMap P φ) :
    (ofTorsor U b P hP φ hφ).U = U ∧ (ofTorsor U b P hP φ hφ).b = b ∧
      (ofTorsor U b P hP φ hφ).P = P ∧ (ofTorsor U b P hP φ hφ).isTorsor = hP ∧
      (ofTorsor U b P hP φ hφ).φ = φ ∧
      (ofTorsor U b P hP φ hφ).equivariant = hφ := sorry

/-- Forget the equivariant map to `X`, retaining the underlying `G_U`-torsor. -/
def toTorsor (ξ : Obj G X) : Torsors.Obj G :=
  Torsors.ofTorsor ξ.U ξ.b ξ.P ξ.isTorsor

/-- The underlying torsor of `ofTorsor` is the supplied torsor data. -/
theorem toTorsor_ofTorsor (U : Over S) (b : ofOver U ⟶ B)
    (P : Action (grpOverPullback G b))
    (hP : IsStandardTorsor (grpOverPullback G b) P .fppf)
    (φ : P.X ⟶ (pullbackAction b G X).X) (hφ : IsEquivariantMap P φ) :
    toTorsor (ofTorsor U b P hP φ hφ) = Torsors.ofTorsor U b P hP := sorry

/-- An isomorphism of underlying objects over `U` is `G_U`-equivariant when it
intertwines the action morphisms after identifying the pulled-back group. -/
def IsEquivariant {ξ ξ' : Obj G X} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.P.X ≅ (overPullback (ofOverMap f)).obj ξ'.P.X) : Prop :=
  ξ.P.mod.smul ≫ g.hom =
    ((eqToHom (congrArg (fun t ↦ (overPullback t).obj G.X) h) ≫
        (overPullbackCompIso ξ'.b (ofOverMap f) G.X).hom) ⊗ₘ g.hom) ≫
      (pullbackAction (ofOverMap f) (grpOverPullback G ξ'.b) ξ'.P).mod.smul

/-- The comparison of pulled-back maps to `X` along a morphism of schemes over `B`. -/
def triangleMap {ξ ξ' : Obj G X} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.P.X ≅ (overPullback (ofOverMap f)).obj ξ'.P.X) :
    ξ.P.X ⟶ (pullbackAction ξ.b G X).X :=
  g.hom ≫ (overPullback (ofOverMap f)).map ξ'.φ ≫
    (overPullbackCompIso ξ'.b (ofOverMap f) X.X).inv ≫
      eqToHom (congrArg (fun t ↦ (overPullback t).obj X.X) h.symm)

/-- A morphism of `[[X/G]]`: a morphism of the underlying `G_U`-torsors whose
isomorphism is compatible with the maps to `X`. -/
structure Hom {G : GroupAlgebraicSpace B} {X : Action G} (ξ ξ' : Obj G X) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism `f` lies over `B`. -/
  comm : ξ.b = ofOverMap f ≫ ξ'.b
  /-- The isomorphism of underlying objects after pullback along `f`. -/
  g : ξ.P.X ≅ (overPullback (ofOverMap f)).obj ξ'.P.X
  /-- The isomorphism `g` is `G_U`-equivariant. -/
  equivariant : IsEquivariant f comm g
  /-- The triangle identity `φ = φ' ∘ g` after pullback along `f`. -/
  triangle : ξ.φ = triangleMap f comm g

/-- Assemble a morphism of `[[X/G]]` from a scheme map, an equivariant
isomorphism of torsors, and the triangle identity. -/
def ofIso {ξ ξ' : Obj G X} (f : ξ.U ⟶ ξ'.U) (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.P.X ≅ (overPullback (ofOverMap f)).obj ξ'.P.X)
    (hg : IsEquivariant f h g) (w : ξ.φ = triangleMap f h g) : Hom ξ ξ' where
  f := f
  comm := h
  g := g
  equivariant := hg
  triangle := w

/-- The constructor of `Hom` stores the supplied scheme map, over-`B` equality,
isomorphism, equivariance, and triangle identity. -/
theorem ofIso_spec {ξ ξ' : Obj G X} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.P.X ≅ (overPullback (ofOverMap f)).obj ξ'.P.X)
    (hg : IsEquivariant f h g) (w : ξ.φ = triangleMap f h g) :
    (ofIso f h g hg w).f = f ∧ (ofIso f h g hg w).comm = h ∧
      (ofIso f h g hg w).g = g ∧ (ofIso f h g hg w).equivariant = hg ∧
      (ofIso f h g hg w).triangle = w := sorry

/-- Identity of schemes over `S` is compatible with the morphism to `B`. -/
theorem id_comm (ξ : Obj G X) : ξ.b = ofOverMap (𝟙 ξ.U) ≫ ξ.b := sorry

/-- The identity comparison of slice objects along `id`. -/
def idIso (ξ : Obj G X) :
    ξ.P.X ≅ (overPullback (ofOverMap (𝟙 ξ.U))).obj ξ.P.X :=
  pullbackAlongIdIso ξ.P.X ≪≫
    eqToIso (congrArg (fun t ↦ (overPullback t).obj ξ.P.X) (ofOverMap_id ξ.U).symm)

/-- The identity comparison of torsors is equivariant. -/
theorem id_equivariant (ξ : Obj G X) :
    IsEquivariant (𝟙 ξ.U) (id_comm ξ) (idIso ξ) := sorry

/-- The identity comparison satisfies the triangle identity. -/
theorem id_triangle (ξ : Obj G X) :
    ξ.φ = triangleMap (𝟙 ξ.U) (id_comm ξ) (idIso ξ) := sorry

/-- Identity morphisms of `[[X/G]]`. -/
def idHom (ξ : Obj G X) : Hom ξ ξ where
  f := 𝟙 ξ.U
  comm := id_comm ξ
  g := idIso ξ
  equivariant := id_equivariant ξ
  triangle := id_triangle ξ

/-- The composite isomorphism of underlying objects along a composite of scheme maps. -/
def compIso {ξ ξ' ξ'' : Obj G X} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.P.X ≅ (overPullback (ofOverMap (α.f ≫ β.f))).obj ξ''.P.X :=
  α.g ≪≫ (overPullback (ofOverMap α.f)).mapIso β.g ≪≫
    (overPullbackCompIso (ofOverMap β.f) (ofOverMap α.f) ξ''.P.X).symm ≪≫
      eqToIso (congrArg (fun t ↦ (overPullback t).obj ξ''.P.X) (ofOverMap_comp α.f β.f).symm)

/-- Compatibility of a composite morphism with the maps to `B`. -/
theorem comp_comm {ξ ξ' ξ'' : Obj G X} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.b = ofOverMap (α.f ≫ β.f) ≫ ξ''.b := sorry

/-- The composite isomorphism of torsors is equivariant. -/
theorem comp_equivariant {ξ ξ' ξ'' : Obj G X} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariant (α.f ≫ β.f) (comp_comm α β) (compIso α β) := sorry

/-- The composite morphism satisfies the triangle identity. -/
theorem comp_triangle {ξ ξ' ξ'' : Obj G X} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.φ = triangleMap (α.f ≫ β.f) (comp_comm α β) (compIso α β) := sorry

/-- Composition of morphisms of `[[X/G]]`. -/
def compHom {ξ ξ' ξ'' : Obj G X} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  comm := comp_comm α β
  g := compIso α β
  equivariant := comp_equivariant α β
  triangle := comp_triangle α β

/-- Left identity law for morphisms of `[[X/G]]`. -/
theorem idHom_comp {ξ ξ' : Obj G X} (α : Hom ξ ξ') : compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `[[X/G]]`. -/
theorem compHom_id {ξ ξ' : Obj G X} (α : Hom ξ ξ') : compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `[[X/G]]`. -/
theorem assocHom {ξ₁ ξ₂ ξ₃ ξ₄ : Obj G X}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (c : Hom ξ₃ ξ₄) :
    compHom (compHom α β) c = compHom α (compHom β c) := sorry

/-- The category of objects of `[[X/G]]`. -/
instance instCategory : Category (Obj G X) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom ξ
  comp α β := compHom α β
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id (ξ : Obj G X) : (idHom ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ξ ξ' ξ'' : Obj G X} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor `[[X/G]] ⟶ (Sch/S)_fppf`. -/
def forget (G : GroupAlgebraicSpace B) (X : Action G) : Obj G X ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, b, P, φ)` to `U`. -/
theorem forget_obj (ξ : Obj G X) : (forget G X).obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ξ ξ' : Obj G X} (α : Hom ξ ξ') : (forget G X).map α = α.f := sorry

/-- The forgetful functor is fibered in groupoids. -/
instance instIsFiberedInGroupoids :
    Functor.IsFibered.InGroupoids (forget G X) := sorry

/-- The forgetful functor is a stack in groupoids on the big fppf site. -/
instance instIsStackInGroupoids :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G X) := sorry

/-- The forgetful functor is a stack on the big fppf site. -/
instance instIsStackOnSite :
    IsStack.OnSite (Scheme.fppfTopology.over S) (forget G X) :=
  IsStack.InGroupoids.toOnSite instIsStackInGroupoids

/-- Remark 8.4.9 condition (4): the fibre of `forget G X` over `U` is essentially
small. -/
theorem fibers_essentiallySmall (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget G X).Fiber U)) := sorry

/-- The stack in groupoids `[[X/G]]` over `(Sch/S)_fppf`. -/
def stack (G : GroupAlgebraicSpace B) (X : Action G) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget G X)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p : (stack G X).p = forget G X := sorry

/-- The forgetful functor on objects of `[[X/G]]` sending `(U, b, P, φ)` to
`(U, b, P)`. -/
def toTorsorsFunctor (G : GroupAlgebraicSpace B) (X : Action G) :
    Obj G X ⥤ Torsors.Obj G where
  obj ξ := toTorsor ξ
  map α := Torsors.ofIso α.f α.comm α.g α.equivariant
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor on objects lies over `(Sch/S)_fppf`. -/
theorem toTorsorsFunctor_w (G : GroupAlgebraicSpace B) (X : Action G) :
    toTorsorsFunctor G X ⋙ Torsors.forget G = forget G X := sorry

/-- The forgetful functor on objects preserves strongly cartesian arrows. -/
theorem toTorsors_preserves (G : GroupAlgebraicSpace B) (X : Action G) :
    (BasedFunctor.ofFunctor (toTorsorsFunctor G X) (toTorsorsFunctor_w G X)).PreservesStronglyCartesian :=
  sorry

/-- Bundle a functor into `[[X/G]]` over `(Sch/S)_fppf` as a cartesian based functor. -/
def cartesianOver {S₁ : Type v} [Category S₁]
    (p₁ : S₁ ⥤ Over S) (F : S₁ ⥤ Obj G X) (w : F ⋙ forget G X = p₁) :
    CartesianBasedFunctor p₁ (forget G X) :=
  CartesianBasedFunctor.ofTargetInGroupoids (BasedFunctor.ofFunctor F w)

/-- The cartesian 1-morphism `[[X/G]] ⟶ G`-Torsors over `(Sch/S)_fppf` forgetting
the equivariant map to `X`. -/
def toTorsors (G : GroupAlgebraicSpace B) (X : Action G) :
    CartesianBasedFunctor (forget G X) (Torsors.forget G) :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor (toTorsorsFunctor G X) (toTorsorsFunctor_w G X))
    (toTorsors_preserves G X)

/-- The underlying functor of `toTorsors` is `toTorsorsFunctor`. -/
theorem toTorsors_toFunctor (G : GroupAlgebraicSpace B) (X : Action G) :
    (toTorsors G X).toFunctor = toTorsorsFunctor G X := sorry

end AlgebraicGeometry.QuotientStack.GroupAction
