/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-!
# Quasi-coherent modules on groupoid schemes

This module defines equivariant quasi-coherent modules on a groupoid scheme, their
morphisms, and the resulting category.
-/

@[expose] public section

open CategoryTheory Limits
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The pseudofunctorial comparison between pullback along a composite and successive
pullbacks of quasi-coherent modules. -/
noncomputable def pullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.QCoh.pullback (f ≫ g) ≅ Scheme.QCoh.pullback g ⋙ Scheme.QCoh.pullback f :=
  Cat.Hom.toNatIso (Scheme.QCoh.pseudofunctor.mapComp g.op.toLoc f.op.toLoc)

/-- Equal scheme morphisms induce canonically isomorphic pullback functors. -/
noncomputable def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    Scheme.QCoh.pullback f ≅ Scheme.QCoh.pullback g :=
  Cat.Hom.toNatIso
    (Scheme.QCoh.pseudofunctor.map₂Iso
      (eqToIso (congrArg (fun k : X ⟶ Y ↦ k.op.toLoc) h)))

/-- Pullback along an identity morphism is canonically isomorphic to the identity functor. -/
noncomputable def pullbackIdIso (X : Scheme.{u}) :
    Scheme.QCoh.pullback (𝟙 X) ≅ 𝟭 (Scheme.QCoh X) :=
  Cat.Hom.toNatIso
    (Scheme.QCoh.pseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op X)))

/-- Pull an action morphism back along a map into its arrow scheme, including the canonical
pseudofunctorial comparison maps. -/
noncomputable def reindexAction {X Y Z : Scheme.{u}} (target source : X ⟶ Y)
    (h : Z ⟶ X) (F : Scheme.QCoh Y)
    (action : (Scheme.QCoh.pullback target).obj F ⟶
      (Scheme.QCoh.pullback source).obj F) :
    (Scheme.QCoh.pullback (h ≫ target)).obj F ⟶
      (Scheme.QCoh.pullback (h ≫ source)).obj F :=
  (pullbackCompIso h target).hom.app F ≫
    (Scheme.QCoh.pullback h).map action ≫
      (pullbackCompIso h source).inv.app F

/-- The first projection from the scheme of composable arrows. -/
def composableFst {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  (pullback.fst G.s G.t).left

/-- The second projection from the scheme of composable arrows. -/
def composableSnd {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  (pullback.snd G.s G.t).left

/-- The composition map on the underlying schemes. -/
def compositionMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  G.c.left

/-- On composable arrows, the source of the first arrow equals the target of the second. -/
theorem composableConditionLeft {S : Scheme.{u}} (G : GroupoidScheme S) :
    composableFst G ≫ G.s.left = composableSnd G ≫ G.t.left := sorry

/-- The target of a composite is the target of the first arrow. -/
theorem compositionTargetLeft {S : Scheme.{u}} (G : GroupoidScheme S) :
    compositionMap G ≫ G.t.left = composableFst G ≫ G.t.left := sorry

/-- The source of a composite is the source of the second arrow. -/
theorem compositionSourceLeft {S : Scheme.{u}} (G : GroupoidScheme S) :
    compositionMap G ≫ G.s.left = composableSnd G ≫ G.s.left := sorry

/-- The target of an identity arrow is the underlying object. -/
theorem identityTargetLeft {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.e.left ≫ G.t.left = 𝟙 G.U.left := sorry

/-- The source of an identity arrow is the underlying object. -/
theorem identitySourceLeft {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.e.left ≫ G.s.left = 𝟙 G.U.left := sorry

/-- The cocycle condition for an equivariance map `t^*F ⟶ s^*F`. -/
def Cocycle {S : Scheme.{u}} (G : GroupoidScheme S) (F : Scheme.QCoh G.U.left)
    (action : (Scheme.QCoh.pullback G.t.left).obj F ⟶
      (Scheme.QCoh.pullback G.s.left).obj F) : Prop :=
  reindexAction G.t.left G.s.left (composableFst G) F action ≫
      (pullbackEqIso (composableConditionLeft G)).hom.app F ≫
        reindexAction G.t.left G.s.left (composableSnd G) F action =
    (pullbackEqIso (compositionTargetLeft G)).inv.app F ≫
      reindexAction G.t.left G.s.left (compositionMap G) F action ≫
        (pullbackEqIso (compositionSourceLeft G)).hom.app F

/-- The unit condition for an equivariance map `t^*F ⟶ s^*F`. -/
def Unit {S : Scheme.{u}} (G : GroupoidScheme S) (F : Scheme.QCoh G.U.left)
    (action : (Scheme.QCoh.pullback G.t.left).obj F ⟶
      (Scheme.QCoh.pullback G.s.left).obj F) : Prop :=
  (pullbackIdIso G.U.left).inv.app F ≫
      (pullbackEqIso (identityTargetLeft G)).inv.app F ≫
        reindexAction G.t.left G.s.left G.e.left F action ≫
          (pullbackEqIso (identitySourceLeft G)).hom.app F ≫
            (pullbackIdIso G.U.left).hom.app F = 𝟙 F

/-- A quasi-coherent module on a groupoid scheme, with its equivariance map, cocycle law,
and unit law. -/
structure System {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The quasi-coherent module on the object scheme. -/
  obj : Scheme.QCoh G.U.left
  /-- The equivariance map `t^*F ⟶ s^*F`. -/
  action : (Scheme.QCoh.pullback G.t.left).obj obj ⟶
    (Scheme.QCoh.pullback G.s.left).obj obj
  /-- The equivariance map satisfies the cocycle condition. -/
  cocycle : Cocycle G obj action
  /-- Pullback of the equivariance map along the identity section is the identity. -/
  unit : Unit G obj action

namespace System

/-- Construct an equivariant quasi-coherent module from its module, action, and laws. -/
def of {S : Scheme.{u}} {G : GroupoidScheme S} (F : Scheme.QCoh G.U.left)
    (action : (Scheme.QCoh.pullback G.t.left).obj F ⟶
      (Scheme.QCoh.pullback G.s.left).obj F)
    (cocycle : Cocycle G F action) (unit : Unit G F action) : System G :=
  ⟨F, action, cocycle, unit⟩

/-- An equivariant quasi-coherent module satisfies its cocycle and unit laws. -/
theorem spec {S : Scheme.{u}} {G : GroupoidScheme S} (A : System G) :
    Cocycle G A.obj A.action ∧ Unit G A.obj A.action := sorry

/-- A morphism of equivariant quasi-coherent modules is a module morphism compatible with
their equivariance maps. -/
structure Hom {S : Scheme.{u}} {G : GroupoidScheme S} (A B : System G) where
  /-- The underlying quasi-coherent-module morphism. -/
  hom : A.obj ⟶ B.obj
  /-- Compatibility with the equivariance maps. -/
  compatibility :
    (Scheme.QCoh.pullback G.t.left).map hom ≫ B.action =
      A.action ≫ (Scheme.QCoh.pullback G.s.left).map hom

namespace Hom

/-- Construct an equivariant morphism from an underlying compatible module morphism. -/
def of {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    (hom : A.obj ⟶ B.obj)
    (compatibility :
      (Scheme.QCoh.pullback G.t.left).map hom ≫ B.action =
        A.action ≫ (Scheme.QCoh.pullback G.s.left).map hom) : Hom A B :=
  ⟨hom, compatibility⟩

/-- Equivariant morphisms are determined by their underlying module morphisms. -/
theorem ext {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    {f g : Hom A B} (h : f.hom = g.hom) : f = g := sorry

/-- The identity module morphism is equivariant. -/
theorem id_compatibility {S : Scheme.{u}} {G : GroupoidScheme S} (A : System G) :
    (Scheme.QCoh.pullback G.t.left).map (𝟙 A.obj) ≫ A.action =
      A.action ≫ (Scheme.QCoh.pullback G.s.left).map (𝟙 A.obj) := sorry

/-- The identity equivariant morphism. -/
def id {S : Scheme.{u}} {G : GroupoidScheme S} (A : System G) : Hom A A :=
  ⟨𝟙 A.obj, id_compatibility A⟩

/-- Compatibility with equivariance is preserved by composition. -/
theorem comp_compatibility {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B C : System G} (f : Hom A B) (g : Hom B C) :
    (Scheme.QCoh.pullback G.t.left).map (f.hom ≫ g.hom) ≫ C.action =
      A.action ≫ (Scheme.QCoh.pullback G.s.left).map (f.hom ≫ g.hom) := sorry

/-- Composition of equivariant morphisms. -/
def comp {S : Scheme.{u}} {G : GroupoidScheme S} {A B C : System G}
    (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨f.hom ≫ g.hom, comp_compatibility f g⟩

/-- Left identity for equivariant morphisms. -/
theorem id_comp {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    (f : Hom A B) : comp (id A) f = f := sorry

/-- Right identity for equivariant morphisms. -/
theorem comp_id {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    (f : Hom A B) : comp f (id B) = f := sorry

/-- Associativity of equivariant morphisms. -/
theorem assoc {S : Scheme.{u}} {G : GroupoidScheme S} {A B C D : System G}
    (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

end System

/-- The explicit category structure on equivariant quasi-coherent systems. -/
@[reducible] def systemCategory {S : Scheme.{u}} (G : GroupoidScheme S) :
    Category (System G) where
  Hom := System.Hom
  id := System.Hom.id
  comp := System.Hom.comp
  id_comp := System.Hom.id_comp
  comp_id := System.Hom.comp_id
  assoc := System.Hom.assoc

/-- The category of equivariant quasi-coherent modules on a groupoid scheme. -/
def QCoh {S : Scheme.{u}} (G : GroupoidScheme S) : Cat :=
  @Cat.of (System G) (systemCategory G)

namespace QCoh

/-- Construct an object of `G.QCoh` from a module, action, cocycle law, and unit law. -/
def of {S : Scheme.{u}} {G : GroupoidScheme S} (F : Scheme.QCoh G.U.left)
    (action : (Scheme.QCoh.pullback G.t.left).obj F ⟶
      (Scheme.QCoh.pullback G.s.left).obj F)
    (cocycle : Cocycle G F action) (unit : Unit G F action) : G.QCoh :=
  System.of F action cocycle unit

/-- The underlying quasi-coherent module of an equivariant object. -/
def obj {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) : Scheme.QCoh G.U.left :=
  System.obj A

/-- The inverse-oriented equivariance morphism obtained by reindexing the action along
groupoid inversion. -/
noncomputable def actionInverse {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) :
    (Scheme.QCoh.pullback G.s.left).obj A.obj ⟶
      (Scheme.QCoh.pullback G.t.left).obj A.obj :=
  (pullbackEqIso
      (congrArg (fun f : G.R ⟶ G.U ↦ f.left) G.inverse_target)).inv.app A.obj ≫
    reindexAction G.t.left G.s.left G.i.left A.obj (System.action A) ≫
      (pullbackEqIso
        (congrArg (fun f : G.R ⟶ G.U ↦ f.left) G.inverse_source)).hom.app A.obj

/-- The action followed by its inversion-induced inverse is the identity. -/
theorem action_comp_actionInverse {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) :
    System.action A ≫ actionInverse A = 𝟙 _ := sorry

/-- The inversion-induced inverse followed by the action is the identity. -/
theorem actionInverse_comp_action {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) :
    actionInverse A ≫ System.action A = 𝟙 _ := sorry

/-- The equivariance map bundled with its inverse induced by groupoid inversion. -/
noncomputable def actionIso {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) :
    (Scheme.QCoh.pullback G.t.left).obj A.obj ≅
      (Scheme.QCoh.pullback G.s.left).obj A.obj where
  hom := System.action A
  inv := actionInverse A
  hom_inv_id := action_comp_actionInverse A
  inv_hom_id := actionInverse_comp_action A

/-- The equivariance map of an equivariant quasi-coherent module. -/
def action {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) :
    (Scheme.QCoh.pullback G.t.left).obj A.obj ⟶
      (Scheme.QCoh.pullback G.s.left).obj A.obj :=
  (actionIso A).hom

/-- The underlying module map of an equivariant morphism. -/
def hom {S : Scheme.{u}} {G : GroupoidScheme S} {A B : G.QCoh} (f : A ⟶ B) :
    A.obj ⟶ B.obj :=
  (f : System.Hom A B).hom

end QCoh

end AlgebraicGeometry.GroupoidScheme
