/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Definition_78_8_1_Action
public import stacks_project.Chap78.Definition_78_9_3_Torsor
public import stacks_project.Chap78.Lemma_78_5_2

/-!
# Fppf torsors under a group algebraic space

The stack in groupoids of fppf `G_U`-torsors for a group algebraic space `G`
over an algebraic space `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism `(Over.map U.hom).obj V ⟶ U` induced by the structure map of `V`. -/
def overMapHom {S : Scheme.{u}} {U : Over S} (V : Over U.left) :
    (Over.map U.hom).obj V ⟶ U :=
  Over.homMk V.hom rfl

/-- `overMapHom V` is `Over.homMk` of the structure morphism of `V`. -/
theorem overMapHom_eq {S : Scheme.{u}} {U : Over S} (V : Over U.left) :
    overMapHom V = Over.homMk V.hom rfl := sorry

/-- Yoneda of an identity morphism of schemes over `S` is the identity. -/
theorem ofOverMap_id {S : Scheme.{u}} (U : Over S) :
    ofOverMap (𝟙 U) = 𝟙 (ofOver U) := sorry

/-- Yoneda of a composite morphism of schemes over `S` is the composite. -/
theorem ofOverMap_comp {S : Scheme.{u}} {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    ofOverMap (f ≫ g) = ofOverMap f ≫ ofOverMap g := sorry

/-- The cone equality for the identity comparison of a slice pullback. -/
theorem pullbackAlongId_w {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) :
    (𝟙 X.left) ≫ X.hom = X.hom ≫ 𝟙 B := sorry

/-- Slice pullback along an identity morphism recovers the original object. -/
def pullbackAlongIdIso {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) :
    X ≅ (overPullback (𝟙 B)).obj X :=
  Over.isoMk
    { hom := pullbackLift X.hom (𝟙 B) (𝟙 X.left) X.hom (pullbackAlongId_w X)
      inv := overPullbackFst (𝟙 B) X
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- The first factor of the composite-pullback comparison. -/
def overPullbackCompToMid {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback (g ≫ f)).obj X).left ⟶ ((overPullback f).obj X).left :=
  pullbackLift X.hom f (overPullbackFst (g ≫ f) X)
    (overPullbackSnd (g ≫ f) X ≫ g) sorry

/-- The cone equality for the composite-pullback comparison. -/
theorem overPullbackComp_w {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompToMid f g X ≫ ((overPullback f).obj X).hom =
      overPullbackSnd (g ≫ f) X ≫ g := sorry

/-- Underlying map of the comparison `(X ×_B B'') ⟶ (X ×_B B') ×_{B'} B''`. -/
def overPullbackCompLeft {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback (g ≫ f)).obj X).left ⟶
      ((overPullback g).obj ((overPullback f).obj X)).left :=
  pullbackLift ((overPullback f).obj X).hom g (overPullbackCompToMid f g X)
    (overPullbackSnd (g ≫ f) X) (overPullbackComp_w f g X)

/-- The comparison of iterated slice pullbacks commutes with the structure morphisms. -/
theorem overPullbackCompLeft_w {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompLeft f g X ≫ ((overPullback g).obj ((overPullback f).obj X)).hom =
      overPullbackSnd (g ≫ f) X := sorry

/-- Inverse underlying map of the comparison of iterated slice pullbacks. -/
def overPullbackCompLeftInv {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback g).obj ((overPullback f).obj X)).left ⟶
      ((overPullback (g ≫ f)).obj X).left :=
  pullbackLift X.hom (g ≫ f)
    (overPullbackFst g ((overPullback f).obj X) ≫ overPullbackFst f X)
    (overPullbackSnd g ((overPullback f).obj X)) sorry

/-- Slice pullback along a composite is the composite of slice pullbacks. -/
def overPullbackCompIso {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    (overPullback (g ≫ f)).obj X ≅ (overPullback g).obj ((overPullback f).obj X) :=
  Over.isoMk
    { hom := overPullbackCompLeft f g X
      inv := overPullbackCompLeftInv f g X
      hom_inv_id := sorry
      inv_hom_id := sorry }
    (overPullbackCompLeft_w f g X)

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The action morphism of a slice-pulled module object. -/
def pullbackActionSmul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (grpOverPullback G f).X ⊗ (Over.pullback f).obj X.X ⟶ (Over.pullback f).obj X.X :=
  Functor.LaxMonoidal.μ (Over.pullback f) G.X X.X ≫ (Over.pullback f).map X.mod.smul

/-- The identity-action law for a slice-pulled module object. -/
theorem pullbackAction_one_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    η[(grpOverPullback G f).X] ⊵ₗ (Over.pullback f).obj X.X ≫ pullbackActionSmul f G X =
      (λₗ ((Over.pullback f).obj X.X)).hom := sorry

/-- The multiplication-action law for a slice-pulled module object. -/
theorem pullbackAction_mul_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    μ[(grpOverPullback G f).X] ⊵ₗ (Over.pullback f).obj X.X ≫ pullbackActionSmul f G X =
      (αₗ (grpOverPullback G f).X (grpOverPullback G f).X
          ((Over.pullback f).obj X.X)).hom ≫
        (grpOverPullback G f).X ⊴ₗ pullbackActionSmul f G X ≫
          pullbackActionSmul f G X := sorry

/-- Slice pullback of a `G`-action along `f : B' ⟶ B`. -/
def pullbackAction {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) : Action (grpOverPullback G f) where
  X := (Over.pullback f).obj X.X
  mod :=
    { smul := pullbackActionSmul f G X
      one_smul := pullbackAction_one_smul f G X
      mul_smul := pullbackAction_mul_smul f G X }

/-- The underlying object of a pulled-back action is the slice pullback of the
original object. -/
theorem pullbackAction_X {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (pullbackAction f G X).X = (Over.pullback f).obj X.X := sorry

namespace Torsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- An object of `G`-Torsors: a scheme `U` over `S`, a morphism `b : U ⟶ B`, and
an fppf `G_U`-torsor. -/
structure Obj (G : GroupAlgebraicSpace B) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The morphism `b : U ⟶ B` of algebraic spaces over `S`. -/
  b : ofOver U ⟶ B
  /-- The fppf `G_U`-torsor over `U`. -/
  X : Action (grpOverPullback G b)
  /-- The action `X` is an fppf `G_U`-torsor in the sense of
  `IsStandardTorsor`. -/
  isTorsor : IsStandardTorsor (grpOverPullback G b) X .fppf

variable {G : GroupAlgebraicSpace B}

/-- Assemble an object of `G`-Torsors from a scheme, a morphism to `B`, and an
fppf torsor. -/
def ofTorsor (U : Over S) (b : ofOver U ⟶ B) (X : Action (grpOverPullback G b))
    (hX : IsStandardTorsor (grpOverPullback G b) X .fppf) : Obj G where
  U := U
  b := b
  X := X
  isTorsor := hX

/-- The constructor of `Obj` stores the supplied scheme, morphism, torsor, and
fppf witness. -/
theorem ofTorsor_spec (U : Over S) (b : ofOver U ⟶ B)
    (X : Action (grpOverPullback G b))
    (hX : IsStandardTorsor (grpOverPullback G b) X .fppf) :
    (ofTorsor U b X hX).U = U ∧ (ofTorsor U b X hX).b = b ∧
      (ofTorsor U b X hX).X = X ∧ (ofTorsor U b X hX).isTorsor = hX := sorry

/-- Comparison of group objects `G_U` and the pullback of `G_{U'}` along `f`. -/
def groupCompare {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b) :
    (grpOverPullback G ξ.b).X ⟶
      ((Over.pullback (ofOverMap f)).mapGrp.obj (grpOverPullback G ξ'.b)).X :=
  eqToHom (congrArg (fun t ↦ (Over.pullback t).obj G.X) h) ≫
    ((Over.pullbackComp (ofOverMap f) ξ'.b).app G.X).hom

/-- An isomorphism of underlying objects over `U` is `G_U`-equivariant when it
intertwines the action morphisms after identifying the pulled-back group. -/
def IsEquivariant {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (Over.pullback (ofOverMap f)).obj ξ'.X.X) : Prop :=
  ξ.X.mod.smul ≫ g.hom =
    (groupCompare f h ⊗ₘ g.hom) ≫ (pullbackAction (ofOverMap f) (grpOverPullback G ξ'.b) ξ'.X).mod.smul

/-- A morphism of `G`-Torsors: a map of schemes over `B` and an equivariant
isomorphism of `G_U`-torsors. -/
structure Hom {G : GroupAlgebraicSpace B} (ξ ξ' : Obj G) where
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
def ofIso {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U) (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (Over.pullback (ofOverMap f)).obj ξ'.X.X)
    (hg : IsEquivariant f h g) : Hom ξ ξ' where
  f := f
  comm := h
  g := g
  equivariant := hg

/-- The constructor of `Hom` stores the supplied scheme map, over-`B` equality,
isomorphism, and equivariance witness. -/
theorem ofIso_spec {ξ ξ' : Obj G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : ξ.X.X ≅ (Over.pullback (ofOverMap f)).obj ξ'.X.X)
    (hg : IsEquivariant f h g) :
    (ofIso f h g hg).f = f ∧ (ofIso f h g hg).comm = h ∧
      (ofIso f h g hg).g = g ∧ (ofIso f h g hg).equivariant = hg := sorry

/-- Identity of schemes over `S` is compatible with the morphism to `B`. -/
theorem id_comm (ξ : Obj G) : ξ.b = ofOverMap (𝟙 ξ.U) ≫ ξ.b := sorry

/-- The identity comparison of slice objects along `id`. -/
def idIso (ξ : Obj G) :
    ξ.X.X ≅ (Over.pullback (ofOverMap (𝟙 ξ.U))).obj ξ.X.X :=
  (Over.pullbackId.app ξ.X.X).symm ≪≫
    eqToIso (congrArg (fun t ↦ (Over.pullback t).obj ξ.X.X) (ofOverMap_id ξ.U).symm)

/-- The identity comparison of torsors is equivariant. -/
theorem id_equivariant (ξ : Obj G) :
    IsEquivariant (𝟙 ξ.U) (id_comm ξ) (idIso ξ) := sorry

/-- Identity morphisms of `G`-Torsors. -/
def idHom (ξ : Obj G) : Hom ξ ξ where
  f := 𝟙 ξ.U
  comm := id_comm ξ
  g := idIso ξ
  equivariant := id_equivariant ξ

/-- The composite isomorphism of underlying objects along a composite of scheme maps. -/
def compIso {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.X.X ≅ (Over.pullback (ofOverMap (α.f ≫ β.f))).obj ξ''.X.X :=
  α.g ≪≫ (Over.pullback (ofOverMap α.f)).mapIso β.g ≪≫
    ((Over.pullbackComp (ofOverMap α.f) (ofOverMap β.f)).app ξ''.X.X).symm ≪≫
      eqToIso (congrArg (fun t ↦ (Over.pullback t).obj ξ''.X.X) (ofOverMap_comp α.f β.f).symm)

/-- Compatibility of a composite morphism with the maps to `B`. -/
theorem comp_comm {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.b = ofOverMap (α.f ≫ β.f) ≫ ξ''.b := sorry

/-- The composite isomorphism of torsors is equivariant. -/
theorem comp_equivariant {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariant (α.f ≫ β.f) (comp_comm α β) (compIso α β) := sorry

/-- Composition of morphisms of `G`-Torsors. -/
def compHom {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  comm := comp_comm α β
  g := compIso α β
  equivariant := comp_equivariant α β

/-- Left identity law for morphisms of `G`-Torsors. -/
theorem idHom_comp {ξ ξ' : Obj G} (α : Hom ξ ξ') : compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `G`-Torsors. -/
theorem compHom_id {ξ ξ' : Obj G} (α : Hom ξ ξ') : compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `G`-Torsors. -/
theorem assocHom {ξ₁ ξ₂ ξ₃ ξ₄ : Obj G} (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (c : Hom ξ₃ ξ₄) :
    compHom (compHom α β) c = compHom α (compHom β c) := sorry

/-- The category of objects of `G`-Torsors. -/
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

end Torsors

end AlgebraicGeometry.GroupAlgebraicSpace
