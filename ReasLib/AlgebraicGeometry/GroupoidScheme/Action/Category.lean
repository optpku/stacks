/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# Actions of groupoid schemes

This module supplies the category of schemes over the object scheme of a groupoid scheme
equipped with an action isomorphism and its unit and cocycle laws.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The action of an arrow `r` on a generalized point `v`, induced by an isomorphism from
the target pullback of `V` to its source pullback. -/
def actionMap {S : Scheme.{u}} (G : GroupoidScheme S) (V : Over G.U)
    (φ : (Over.pullback G.t).obj V ≅ (Over.pullback G.s).obj V)
    {T : Over S} (v : T ⟶ V.left) (r : T ⟶ G.R)
    (h : v ≫ V.hom = r ≫ G.t) : T ⟶ V.left :=
  pullback.lift v r h ≫ φ.hom.left ≫ pullback.fst V.hom G.s

/-- The action map induced by `φ` lies over the source of the acting arrow. -/
theorem actionMap_over_source {S : Scheme.{u}} (G : GroupoidScheme S) (V : Over G.U)
    (φ : (Over.pullback G.t).obj V ≅ (Over.pullback G.s).obj V)
    {T : Over S} (v : T ⟶ V.left) (r : T ⟶ G.R)
    (h : v ≫ V.hom = r ≫ G.t) :
    actionMap G V φ v r h ≫ V.hom = r ≫ G.s := sorry

namespace Action

/-- The identity-arrow law for an action isomorphism on a scheme over `G.U`. -/
def IsUnital {S : Scheme.{u}} (G : GroupoidScheme S) (V : Over G.U)
    (φ : (Over.pullback G.t).obj V ≅ (Over.pullback G.s).obj V) : Prop :=
  ∀ (T : Over S) (v : T ⟶ V.left)
    (h : v ≫ V.hom = (v ≫ V.hom ≫ G.e) ≫ G.t),
    actionMap G V φ v (v ≫ V.hom ≫ G.e) h = v

/-- The composition law for an action isomorphism on a scheme over `G.U`. -/
def IsCocycle {S : Scheme.{u}} (G : GroupoidScheme S) (V : Over G.U)
    (φ : (Over.pullback G.t).obj V ≅ (Over.pullback G.s).obj V) : Prop :=
  ∀ (T : Over S) (v : T ⟶ V.left) (r₀ r₁ : T ⟶ G.R)
    (hv : v ≫ V.hom = r₀ ≫ G.t) (hr : r₀ ≫ G.s = r₁ ≫ G.t)
    (hnext : actionMap G V φ v r₀ hv ≫ V.hom = r₁ ≫ G.t)
    (hcomp : v ≫ V.hom = (pullback.lift r₀ r₁ hr ≫ G.c) ≫ G.t),
    actionMap G V φ (actionMap G V φ v r₀ hv) r₁ hnext =
      actionMap G V φ v (pullback.lift r₀ r₁ hr ≫ G.c) hcomp

/-- A scheme over the object scheme of `G`, equipped with an action isomorphism and its
unit and cocycle laws. -/
structure System {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The scheme over the object scheme. -/
  V : Over G.U
  /-- The action isomorphism over the arrow scheme. -/
  iso : (Over.pullback G.t).obj V ≅ (Over.pullback G.s).obj V
  /-- The action isomorphism satisfies the identity-arrow law. -/
  unit : IsUnital G V iso
  /-- The action isomorphism satisfies the composition law. -/
  cocycle : IsCocycle G V iso

namespace System

/-- Construct an action system from a scheme, its action isomorphism, and its two laws. -/
def ofIso {S : Scheme.{u}} (G : GroupoidScheme S) (V : Over G.U)
    (φ : (Over.pullback G.t).obj V ≅ (Over.pullback G.s).obj V)
    (unit : IsUnital G V φ) (cocycle : IsCocycle G V φ) : System G where
  V := V
  iso := φ
  unit := unit
  cocycle := cocycle

/-- The two defining laws carried by an action system. -/
theorem spec {S : Scheme.{u}} {G : GroupoidScheme S} (A : System G) :
    IsUnital G A.V A.iso ∧ IsCocycle G A.V A.iso := sorry

/-- A morphism of action systems is a map over `G.U` compatible with their action
isomorphisms. -/
structure Hom {S : Scheme.{u}} {G : GroupoidScheme S} (A B : System G) where
  /-- The underlying map over `G.U`. -/
  map : A.V ⟶ B.V
  /-- The underlying map forms the canonical commutative square with the action isomorphisms. -/
  compatibility :
    CommSq A.iso.hom ((Over.pullback G.t).map map) ((Over.pullback G.s).map map) B.iso.hom

namespace Hom

/-- Construct a morphism of action systems from a compatible map over `G.U`. -/
def ofMap {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    (f : A.V ⟶ B.V)
    (compatibility :
      CommSq A.iso.hom ((Over.pullback G.t).map f) ((Over.pullback G.s).map f) B.iso.hom) :
    Hom A B where
  map := f
  compatibility := compatibility

/-- The action-morphism square as an equality of composites. -/
theorem compatibility_w {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    (f : Hom A B) :
    A.iso.hom ≫ (Over.pullback G.s).map f.map =
      (Over.pullback G.t).map f.map ≫ B.iso.hom :=
  f.compatibility.w

/-- Action-system morphisms are determined by their underlying maps. -/
theorem ext {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    {f g : Hom A B} (h : f.map = g.map) : f = g := sorry

/-- The identity map satisfies action compatibility. -/
theorem id_compatibility {S : Scheme.{u}} {G : GroupoidScheme S} (A : System G) :
    CommSq A.iso.hom ((Over.pullback G.t).map (𝟙 A.V))
      ((Over.pullback G.s).map (𝟙 A.V)) A.iso.hom := sorry

/-- The identity morphism of an action system. -/
def id {S : Scheme.{u}} {G : GroupoidScheme S} (A : System G) : Hom A A where
  map := 𝟙 A.V
  compatibility := id_compatibility A

/-- Action compatibility is preserved by composition. -/
theorem comp_compatibility {S : Scheme.{u}} {G : GroupoidScheme S} {A B C : System G}
    (f : Hom A B) (g : Hom B C) :
    CommSq A.iso.hom ((Over.pullback G.t).map (f.map ≫ g.map))
      ((Over.pullback G.s).map (f.map ≫ g.map)) C.iso.hom := sorry

/-- Composition of morphisms of action systems. -/
def comp {S : Scheme.{u}} {G : GroupoidScheme S} {A B C : System G}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  map := f.map ≫ g.map
  compatibility := comp_compatibility f g

/-- Left identity for morphisms of action systems. -/
theorem id_comp {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    (f : Hom A B) : comp (id A) f = f := sorry

/-- Right identity for morphisms of action systems. -/
theorem comp_id {S : Scheme.{u}} {G : GroupoidScheme S} {A B : System G}
    (f : Hom A B) : comp f (id B) = f := sorry

/-- Associativity for morphisms of action systems. -/
theorem assoc {S : Scheme.{u}} {G : GroupoidScheme S} {A B C D : System G}
    (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

end System

/-- The explicit category structure on action systems for `G`. -/
@[reducible] def systemCategory {S : Scheme.{u}} (G : GroupoidScheme S) :
    Category (System G) where
  Hom := System.Hom
  id := System.Hom.id
  comp := System.Hom.comp
  id_comp := System.Hom.id_comp
  comp_id := System.Hom.comp_id
  assoc := System.Hom.assoc

end Action

/-- The category of schemes over `G.U` equipped with a groupoid-action isomorphism. -/
def Action {S : Scheme.{u}} (G : GroupoidScheme S) : Cat :=
  @Cat.of (Action.System G) (Action.systemCategory G)

namespace Action

/-- Construct an object of `Action G` from a scheme, its action isomorphism, and its laws. -/
def ofIso {S : Scheme.{u}} (G : GroupoidScheme S) (V : Over G.U)
    (φ : (Over.pullback G.t).obj V ≅ (Over.pullback G.s).obj V)
    (unit : IsUnital G V φ) (cocycle : IsCocycle G V φ) : Action G :=
  System.ofIso G V φ unit cocycle

/-- The underlying scheme over `G.U` of a groupoid action. -/
def obj {S : Scheme.{u}} {G : GroupoidScheme S} (A : Action G) : Over G.U := A.V

/-- The target-to-source pullback isomorphism of a groupoid action. -/
def iso {S : Scheme.{u}} {G : GroupoidScheme S} (A : Action G) :
    (Over.pullback G.t).obj (obj A) ≅ (Over.pullback G.s).obj (obj A) := A.iso

/-- A groupoid action satisfies the identity-arrow law. -/
theorem unit {S : Scheme.{u}} {G : GroupoidScheme S} (A : Action G) :
    IsUnital G (obj A) (iso A) := sorry

/-- A groupoid action satisfies the composition law. -/
theorem cocycle {S : Scheme.{u}} {G : GroupoidScheme S} (A : Action G) :
    IsCocycle G (obj A) (iso A) := sorry

/-- The underlying map over `G.U` of a morphism of groupoid actions. -/
def hom {S : Scheme.{u}} {G : GroupoidScheme S} {A B : Action G} (f : A ⟶ B) :
    obj A ⟶ obj B := f.map

/-- The underlying map of an action morphism forms the canonical commutative square with the
action isomorphisms. -/
theorem homCompatibility {S : Scheme.{u}} {G : GroupoidScheme S} {A B : Action G}
    (f : A ⟶ B) :
    CommSq (iso A).hom ((Over.pullback G.t).map (hom f))
      ((Over.pullback G.s).map (hom f)) (iso B).hom := by
  exact f.compatibility

/-- The action-morphism square as an equality of composites. -/
theorem homCompatibility_w {S : Scheme.{u}} {G : GroupoidScheme S} {A B : Action G}
    (f : A ⟶ B) :
    (iso A).hom ≫ (Over.pullback G.s).map (hom f) =
      (Over.pullback G.t).map (hom f) ≫ (iso B).hom :=
  (homCompatibility f).w

/-- Morphisms of groupoid actions are determined by their underlying maps. -/
theorem homExt {S : Scheme.{u}} {G : GroupoidScheme S} {A B : Action G}
    {f g : A ⟶ B} (h : hom f = hom g) : f = g := sorry

end Action

end AlgebraicGeometry.GroupoidScheme
