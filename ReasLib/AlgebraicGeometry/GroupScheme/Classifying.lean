/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.CategoryTheory.Sites.Torsor.Basic

/-!
# Classifying stack of fppf torsors under a group scheme

The classifying stack of a group scheme `G` over `S` is the category fibred in
groupoids of fppf `G`-torsors, with projection to `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupScheme
namespace Classifying

variable {S : Scheme.{u}}

/-- Restriction of an fppf sheaf of types from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrict (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map U.hom).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of types along a morphism in `Over S`. -/
def inverseImage {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map f.left).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Inverse image along an identity morphism of `Over S` is the identity functor. -/
def inverseImageId (U : Over S) :
    inverseImage (𝟙 U) ≅ 𝟭 (Sheaf (Scheme.fppfTopology.over U.left) (Type u)) :=
  Functor.sheafPushforwardContinuousId' (Over.mapId U.left) (Type u)
    (Scheme.fppfTopology.over U.left)

/-- Inverse image is contravariant for composition in `Over S`. -/
def inverseImageComp {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    inverseImage g ⋙ inverseImage f ≅ inverseImage (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f.left g.left).symm (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over U''.left)

/-- Morphisms into the base-changed group scheme over `U` correspond to
morphisms into `G` over `S`. -/
def groupHomEquiv (G : GroupScheme S) (U : Over S) (V : Over U.left) :
    (V ⟶ ((Over.pullback U.hom).mapGrp.obj G).X) ≃ ((Over.map U.hom).obj V ⟶ G.X) :=
  ((Over.mapPullbackAdj U.hom).homEquiv V G.X).symm

/-- Sections of the represented fppf group sheaf of `G_U` are multiplicatively
equivalent to morphisms into `G` over `S`. -/
def groupSectionsMulEquiv (G : GroupScheme S) (U : Over S) (V : Over U.left) :
    (representableGroup .fppf ((Over.pullback U.hom).mapGrp.obj G)).1.obj (op V) ≃*
      (yonedaGrp.obj G).obj (op ((Over.map U.hom).obj V)) where
  toEquiv := groupHomEquiv G U V
  map_mul' := sorry

/-- Composing `V → U → S` or `V → U → U' → S` yields the same object of `Over S`. -/
def baseOverIso {U U' : Over S} (f : U ⟶ U') (V : Over U.left) :
    (Over.map U.hom).obj V ≅ (Over.map U'.hom).obj ((Over.map f.left).obj V) :=
  Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans
      ((Category.assoc V.hom f.left U'.hom).trans
        (congrArg (fun t => V.hom ≫ t) (Over.w f))))

/-- Group sections of `G_U` and of `G_{U'}` agree after inverse image along `f`. -/
def groupMulEquiv (G : GroupScheme S) {U U' : Over S} (f : U ⟶ U') (V : Over U.left) :
    (representableGroup .fppf ((Over.pullback U.hom).mapGrp.obj G)).1.obj (op V) ≃*
      (representableGroup .fppf ((Over.pullback U'.hom).mapGrp.obj G)).1.obj
        (op ((Over.map f.left).obj V)) :=
  (groupSectionsMulEquiv G U V).trans <|
    (Iso.groupIsoToMulEquiv ((yonedaGrp.obj G).mapIso (baseOverIso f V).symm.op)).trans
      (groupSectionsMulEquiv G U' ((Over.map f.left).obj V)).symm

/-- An object of the classifying stack: a scheme over `S` with an fppf torsor
under the base change of `G`. -/
structure Obj (G : GroupScheme S) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The fppf torsor under `G_U`. -/
  P : Sheaf.Torsor (representableGroup .fppf ((Over.pullback U.hom).mapGrp.obj G))

/-- The group acting on an object over `U` is the base change of `G` along `U → S`. -/
theorem objGroup_eq_baseChange (G : GroupScheme S) (U : Over S) :
    (Over.pullback U.hom).mapGrp.obj G = baseChange G U.hom := sorry

/-- Assemble an object of the classifying stack from a scheme and an fppf torsor. -/
def ofTorsor {G : GroupScheme S} (U : Over S)
    (P : Sheaf.Torsor (representableGroup .fppf ((Over.pullback U.hom).mapGrp.obj G))) : Obj G where
  U := U
  P := P

/-- The constructor of `Obj` stores the supplied scheme and torsor. -/
theorem ofTorsor_spec {G : GroupScheme S} (U : Over S)
    (P : Sheaf.Torsor (representableGroup .fppf ((Over.pullback U.hom).mapGrp.obj G))) :
    (ofTorsor U P).U = U ∧ (ofTorsor U P).P = P := sorry

/-- A carrier isomorphism over `f` is equivariant if it intertwines the
`G`-actions after identifying group sections along inverse image. -/
def IsEquivariant {G : GroupScheme S} {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier) : Prop :=
  ∀ (V : Over ξ.U.left)
    (γ : (representableGroup .fppf ((Over.pullback ξ.U.hom).mapGrp.obj G)).1.obj (op V))
    (x : ξ.P.carrier.1.obj (op V)),
    g.hom.hom.app (op V) ((ξ.P.mulAction V).smul γ x) =
      (ξ'.P.mulAction ((Over.map f.left).obj V)).smul (groupMulEquiv G f V γ)
        (g.hom.hom.app (op V) x)

/-- A morphism of classifying-stack objects: a map of schemes over `S` and an
equivariant isomorphism of torsor carriers. -/
structure Hom {G : GroupScheme S} (ξ ξ' : Obj G) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The isomorphism of torsor carriers after inverse image. -/
  g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier
  /-- The isomorphism `g` is equivariant for the `G`-actions. -/
  equivariant : IsEquivariant f g

/-- Assemble a morphism from a scheme map and an equivariant carrier isomorphism. -/
def ofIso {G : GroupScheme S} {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier) (h : IsEquivariant f g) :
    Hom ξ ξ' where
  f := f
  g := g
  equivariant := h

/-- The constructor of `Hom` stores the supplied scheme map, isomorphism, and
equivariance witness. -/
theorem ofIso_spec {G : GroupScheme S} {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier) (h : IsEquivariant f g) :
    (ofIso f g h).f = f ∧ (ofIso f g h).g = g ∧ (ofIso f g h).equivariant = h := sorry

/-- The identity comparison of torsor carriers is equivariant. -/
theorem id_equivariant {G : GroupScheme S} (ξ : Obj G) :
    IsEquivariant (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := sorry

/-- Identity morphisms of the classifying stack. -/
def idHom {G : GroupScheme S} (ξ : Obj G) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := id_equivariant ξ

/-- The composite isomorphism of torsor carriers along a composite of scheme maps. -/
def compIso {G : GroupScheme S} {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.P.carrier ≅ (inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier :=
  α.g ≪≫ (inverseImage α.f).mapIso β.g ≪≫
    (inverseImageComp α.f β.f).app ξ''.P.carrier

/-- The composite isomorphism of torsor carriers is equivariant. -/
theorem comp_equivariant {G : GroupScheme S} {ξ ξ' ξ'' : Obj G}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariant (α.f ≫ β.f) (compIso α β) := sorry

/-- Composition of morphisms of the classifying stack. -/
def compHom {G : GroupScheme S} {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := compIso α β
  equivariant := comp_equivariant α β

/-- Left identity law for morphisms of the classifying stack. -/
theorem idHom_comp {G : GroupScheme S} {ξ ξ' : Obj G} (α : Hom ξ ξ') :
    compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of the classifying stack. -/
theorem compHom_id {G : GroupScheme S} {ξ ξ' : Obj G} (α : Hom ξ ξ') :
    compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of the classifying stack. -/
theorem assocHom {G : GroupScheme S} {ξ₁ ξ₂ ξ₃ ξ₄ : Obj G}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    compHom (compHom α β) γ = compHom α (compHom β γ) := sorry

/-- The category of objects of the classifying stack of `G`. -/
@[reducible]
def category (G : GroupScheme S) : Category (Obj G) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom ξ
  comp α β := compHom α β
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- The bundled category of schemes over `S` equipped with fppf `G`-torsors. -/
def cat (G : GroupScheme S) : Cat.{u + 1, u + 1} :=
  ⟨Obj G, category G⟩

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id {G : GroupScheme S} (ξ : Obj G) : (idHom ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {G : GroupScheme S} {ξ ξ' ξ'' : Obj G}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor from the classifying stack to `(Sch/S)_fppf`. -/
def forget (G : GroupScheme S) : cat G ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, P)` to `U`. -/
theorem forget_obj {G : GroupScheme S} (ξ : Obj G) : (forget G).obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {G : GroupScheme S} {ξ ξ' : Obj G} (α : Hom ξ ξ') :
    (forget G).map α = α.f := sorry

/-- The forgetful functor is fibered in groupoids. -/
instance instIsFiberedInGroupoids (G : GroupScheme S) :
    Functor.IsFibered.InGroupoids (forget G) := sorry

/-- The forgetful functor is a stack in groupoids on the big fppf site. -/
instance instIsStackInGroupoids (G : GroupScheme S) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G) := sorry

/-- The stack in groupoids of fppf `G`-torsors over `(Sch/S)_fppf`. -/
def stack (G : GroupScheme S) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget G)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (G : GroupScheme S) : (stack G).p = forget G := sorry

end Classifying

/-- The classifying stack of fppf `G`-torsors, as a category fibred in groupoids
over `(Sch/S)_fppf`. -/
def classifyingStack {S : Scheme.{u}} (G : GroupScheme S) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (Classifying.forget G)

/-- The projection of `classifyingStack G` is the forgetful functor on objects. -/
theorem classifyingStack_p {S : Scheme.{u}} (G : GroupScheme S) :
    (classifyingStack G).p = Classifying.forget G := sorry

end AlgebraicGeometry.GroupScheme
