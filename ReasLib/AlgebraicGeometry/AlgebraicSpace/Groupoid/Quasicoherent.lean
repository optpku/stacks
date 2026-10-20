/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pullback

/-!
# Quasi-coherent modules on groupoids in algebraic spaces

Equivariant quasi-coherent modules on a groupoid in algebraic spaces, together with the
canonical comparison isomorphisms for ordinary quasi-coherent pullback along morphisms of
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Equal morphisms of algebraic spaces induce canonically isomorphic pullback functors on
quasi-coherent modules. -/
def pullbackEqIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g) :
    AlgebraicSpace.QCoh.pullback f ≅ AlgebraicSpace.QCoh.pullback g :=
  eqToIso (congrArg AlgebraicSpace.QCoh.pullback h)

/-- Pullback of quasi-coherent modules along an identity morphism is canonically isomorphic
to the identity functor, by lifting `SmallEtaleModuleGlueing.modulesPullbackId`. -/
def pullbackIdIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace.QCoh.pullback (𝟙 X) ≅ 𝟭 (AlgebraicSpace.QCoh X) :=
  NatIso.ofComponents
    (fun F ↦
      (AlgebraicSpace.quasiCoherentModuleProperty X).isoMk
        ((AlgebraicSpace.SmallEtaleModuleGlueing.modulesPullbackId X).app F.obj))
    sorry

/-- Pull an action morphism back along a map into its arrow space, including the canonical
comparison maps. -/
def reindexAction {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (target source : X ⟶ Y)
    (h : Z ⟶ X) (F : AlgebraicSpace.QCoh Y)
    (action : (AlgebraicSpace.QCoh.pullback target).obj F ⟶
      (AlgebraicSpace.QCoh.pullback source).obj F) :
    (AlgebraicSpace.QCoh.pullback (h ≫ target)).obj F ⟶
      (AlgebraicSpace.QCoh.pullback (h ≫ source)).obj F :=
  ((AlgebraicSpace.QCoh.pullbackCompIso target h).symm).hom.app F ≫
    (AlgebraicSpace.QCoh.pullback h).map action ≫
      ((AlgebraicSpace.QCoh.pullbackCompIso source h).symm).inv.app F

/-- The first projection from the space of composable arrows. -/
def composableFst {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  (pullback.fst G.s G.t).left

/-- The second projection from the space of composable arrows. -/
def composableSnd {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  (pullback.snd G.s G.t).left

/-- The composition map on the underlying algebraic spaces. -/
def compositionMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  G.c.left

/-- On composable arrows, the source of the first arrow equals the target of the second. -/
theorem composableConditionLeft {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    composableFst G ≫ G.s.left = composableSnd G ≫ G.t.left := sorry

/-- The target of a composite is the target of the first arrow. -/
theorem compositionTargetLeft {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    compositionMap G ≫ G.t.left = composableFst G ≫ G.t.left := sorry

/-- The source of a composite is the source of the second arrow. -/
theorem compositionSourceLeft {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    compositionMap G ≫ G.s.left = composableSnd G ≫ G.s.left := sorry

/-- The target of an identity arrow is the underlying object. -/
theorem identityTargetLeft {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.e.left ≫ G.t.left = 𝟙 G.U.left := sorry

/-- The source of an identity arrow is the underlying object. -/
theorem identitySourceLeft {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.e.left ≫ G.s.left = 𝟙 G.U.left := sorry

/-- The cocycle condition for an equivariance map `t^* F ⟶ s^* F`. -/
def Cocycle {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F) : Prop :=
  reindexAction G.t.left G.s.left (composableFst G) F action ≫
      (pullbackEqIso (composableConditionLeft G)).hom.app F ≫
        reindexAction G.t.left G.s.left (composableSnd G) F action =
    (pullbackEqIso (compositionTargetLeft G)).inv.app F ≫
      reindexAction G.t.left G.s.left (compositionMap G) F action ≫
        (pullbackEqIso (compositionSourceLeft G)).hom.app F

/-- The unit condition for an equivariance map `t^* F ⟶ s^* F`. -/
def Unit {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F) : Prop :=
  (pullbackIdIso G.U.left).inv.app F ≫
      (pullbackEqIso (identityTargetLeft G)).inv.app F ≫
        reindexAction G.t.left G.s.left G.e.left F action ≫
          (pullbackEqIso (identitySourceLeft G)).hom.app F ≫
            (pullbackIdIso G.U.left).hom.app F =
    𝟙 F

/-- A quasi-coherent module on a groupoid in algebraic spaces, with its equivariance map,
cocycle law, and unit law. -/
structure System {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) where
  /-- The underlying quasi-coherent module on the space of objects. -/
  obj : AlgebraicSpace.QCoh G.U.left
  /-- The equivariance map `t^* F ⟶ s^* F`. -/
  action : (AlgebraicSpace.QCoh.pullback G.t.left).obj obj ⟶
    (AlgebraicSpace.QCoh.pullback G.s.left).obj obj
  /-- The equivariance map satisfies the cocycle condition. -/
  cocycle : Cocycle G obj action
  /-- Pullback of the equivariance map along the identity section is the identity. -/
  unit : Unit G obj action

namespace System

/-- Construct an equivariant quasi-coherent module from its module, action, and laws. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F)
    (cocycle : Cocycle G F action) (unit : Unit G F action) : System G :=
  ⟨F, action, cocycle, unit⟩

/-- An equivariant quasi-coherent module satisfies its cocycle and unit laws. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (A : System G) :
    Cocycle G A.obj A.action ∧ Unit G A.obj A.action := sorry

/-- A morphism of equivariant quasi-coherent modules is a module morphism compatible with
their equivariance maps. -/
structure Hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (M N : System G) where
  /-- The underlying quasi-coherent-module morphism. -/
  hom : M.obj ⟶ N.obj
  /-- Compatibility with the equivariance maps. -/
  compatibility :
    (AlgebraicSpace.QCoh.pullback G.t.left).map hom ≫ N.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map hom

namespace Hom

/-- Construct an equivariant morphism from an underlying compatible module morphism. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N : System G} (hom : M.obj ⟶ N.obj)
    (compatibility :
      (AlgebraicSpace.QCoh.pullback G.t.left).map hom ≫ N.action =
        M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map hom) : Hom M N :=
  ⟨hom, compatibility⟩

/-- Equivariant morphisms are determined by their underlying module morphisms. -/
theorem ext {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N : System G} {f g : Hom M N} (h : f.hom = g.hom) : f = g := sorry

/-- The identity module morphism is equivariant. -/
theorem id_compatibility {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (A : System G) :
    (AlgebraicSpace.QCoh.pullback G.t.left).map (𝟙 A.obj) ≫ A.action =
      A.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (𝟙 A.obj) := sorry

/-- The identity equivariant morphism. -/
def id {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (A : System G) : Hom A A :=
  ⟨𝟙 A.obj, id_compatibility A⟩

/-- Compatibility with equivariance is preserved by composition. -/
theorem comp_compatibility {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {M N P : System G} (f : Hom M N) (g : Hom N P) :
    (AlgebraicSpace.QCoh.pullback G.t.left).map (f.hom ≫ g.hom) ≫ P.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (f.hom ≫ g.hom) := sorry

/-- Composition of equivariant morphisms. -/
def comp {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N P : System G} (f : Hom M N) (g : Hom N P) : Hom M P :=
  ⟨f.hom ≫ g.hom, comp_compatibility f g⟩

/-- Left identity for equivariant morphisms. -/
theorem id_comp {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N : System G} (f : Hom M N) : comp (id M) f = f := sorry

/-- Right identity for equivariant morphisms. -/
theorem comp_id {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N : System G} (f : Hom M N) : comp f (id N) = f := sorry

/-- Associativity of equivariant morphisms. -/
theorem assoc {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N P Q : System G} (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

end System

/-- The explicit category structure on equivariant quasi-coherent systems. -/
@[reducible] def systemCategory {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : Category (System G) where
  Hom := System.Hom
  id := System.Hom.id
  comp := System.Hom.comp
  id_comp := System.Hom.id_comp
  comp_id := System.Hom.comp_id
  assoc := System.Hom.assoc

/-- The category of equivariant quasi-coherent modules on a groupoid in algebraic spaces. -/
def QCoh {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) : Cat :=
  @Cat.of (System G) (systemCategory G)

namespace QCoh

/-- Construct an object of `G.QCoh` from a module, action, cocycle law, and unit law. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F)
    (cocycle : Cocycle G F action) (unit : Unit G F action) : G.QCoh :=
  System.of F action cocycle unit

/-- The underlying quasi-coherent module of an equivariant object. -/
def obj {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (A : G.QCoh) : AlgebraicSpace.QCoh G.U.left :=
  System.obj A

/-- The equivariance map of an equivariant quasi-coherent module. -/
def action {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (A : G.QCoh) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj :=
  System.action A

/-- The underlying module map of an equivariant morphism. -/
def hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N : G.QCoh} (f : M ⟶ N) : M.obj ⟶ N.obj :=
  (f : System.Hom M N).hom

end QCoh

end AlgebraicGeometry.GroupoidAlgebraicSpace
