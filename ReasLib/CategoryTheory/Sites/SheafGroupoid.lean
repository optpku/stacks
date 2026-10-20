/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Internal groupoids in sheaves

An internal groupoid over a sheaf has its objects, arrows, and operations in the
slice over that sheaf. Its sections form an explicit presheaf of groupoids.
-/

@[expose] public section

noncomputable section

universe u v a u' v'

namespace CategoryTheory

open Limits Opposite

namespace SheafGroupoid

/-- The endpoint, unit, inverse, and associativity equations for internal groupoid
operations in a category with pullbacks. The generalized-arrow equations express
the unit, inverse, and associativity diagrams without choosing iterated pullbacks. -/
def Laws {E : Type u} [Category.{v} E] [HasPullbacks E]
    {U R : E} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback t s ⟶ R) : Prop :=
  (e ≫ s = 𝟙 U) ∧ (e ≫ t = 𝟙 U) ∧
  (i ≫ s = t) ∧ (i ≫ t = s) ∧
  (c ≫ s = pullback.fst t s ≫ s) ∧
  (c ≫ t = pullback.snd t s ≫ t) ∧
  (∀ (X : E) (r : X ⟶ R) (h : (r ≫ s ≫ e) ≫ t = r ≫ s),
    pullback.lift (r ≫ s ≫ e) r h ≫ c = r) ∧
  (∀ (X : E) (r : X ⟶ R) (h : r ≫ t = (r ≫ t ≫ e) ≫ s),
    pullback.lift r (r ≫ t ≫ e) h ≫ c = r) ∧
  (∀ (X : E) (r : X ⟶ R) (h : r ≫ t = (r ≫ i) ≫ s),
    pullback.lift r (r ≫ i) h ≫ c = r ≫ s ≫ e) ∧
  (∀ (X : E) (r : X ⟶ R) (h : (r ≫ i) ≫ t = r ≫ s),
    pullback.lift (r ≫ i) r h ≫ c = r ≫ t ≫ e) ∧
  (∀ (X : E) (r₁ r₂ r₃ : X ⟶ R)
      (h₁₂ : r₁ ≫ t = r₂ ≫ s) (h₂₃ : r₂ ≫ t = r₃ ≫ s)
      (hL : (pullback.lift r₁ r₂ h₁₂ ≫ c) ≫ t = r₃ ≫ s)
      (hR : r₁ ≫ t = (pullback.lift r₂ r₃ h₂₃ ≫ c) ≫ s),
    pullback.lift (pullback.lift r₁ r₂ h₁₂ ≫ c) r₃ hL ≫ c =
      pullback.lift r₁ (pullback.lift r₂ r₃ h₂₃ ≫ c) hR ≫ c)

end SheafGroupoid

/-- An internal groupoid in sheaves over a fixed base sheaf, with explicit
object and arrow sheaves, operations over the base, and all groupoid laws. -/
structure SheafGroupoid {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Sheaf J (Type a))
    [HasPullbacks (Sheaf J (Type a))] where
  /-- The object sheaf over the base. -/
  U : Over B
  /-- The arrow sheaf over the base. -/
  R : Over B
  /-- The source morphism over the base. -/
  s : R ⟶ U
  /-- The target morphism over the base. -/
  t : R ⟶ U
  /-- The identity morphism over the base. -/
  e : U ⟶ R
  /-- The inversion morphism over the base. -/
  i : R ⟶ R
  /-- Composition of an arrow followed by an arrow with matching source. -/
  c : pullback t s ⟶ R
  /-- The operations satisfy the internal groupoid equations. -/
  laws : SheafGroupoid.Laws s t e i c

namespace SheafGroupoid

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {B : Sheaf J (Type a)} [HasPullbacks (Sheaf J (Type a))]

/-- Evaluation of an object over a sheaf at an object of the site. -/
abbrev evaluation (B : Sheaf J (Type a)) (T : C) : Over B ⥤ Type a :=
  Over.forget B ⋙ sheafToPresheaf J (Type a) ⋙
    (CategoryTheory.evaluation Cᵒᵖ (Type a)).obj (op T)

/-- An arrow between two sections is an arrow section with those endpoints. -/
structure PointHom (G : SheafGroupoid J B) {T : C}
    (x y : G.U.left.obj.obj (op T)) where
  /-- The underlying section of the arrow sheaf. -/
  arrow : G.R.left.obj.obj (op T)
  /-- The section has the specified source. -/
  source : G.s.left.hom.app (op T) arrow = x
  /-- The section has the specified target. -/
  target : G.t.left.hom.app (op T) arrow = y

namespace PointHom

variable {G : SheafGroupoid J B} {T T' : C}
variable {x y z : G.U.left.obj.obj (op T)}

private theorem hext {x' y' : G.U.left.obj.obj (op T)}
    (f : PointHom G x y) (g : PointHom G x' y')
    (hx : x = x') (hy : y = y') (h : f.arrow = g.arrow) : HEq f g := by
  cases hx
  cases hy
  cases f
  cases g
  cases h
  rfl

/-- An identity section has the original section as both endpoints. -/
theorem id_endpoints (G : SheafGroupoid J B) (x : G.U.left.obj.obj (op T)) :
    G.s.left.hom.app (op T) (G.e.left.hom.app (op T) x) = x ∧
    G.t.left.hom.app (op T) (G.e.left.hom.app (op T) x) = x := by
  sorry

/-- The identity arrow of a section. -/
def id (x : G.U.left.obj.obj (op T)) : PointHom G x x :=
  ⟨G.e.left.hom.app (op T) x, (id_endpoints G x).1, (id_endpoints G x).2⟩

/-- Successive arrow sections have matching target and source. -/
theorem comp_compatible (f : PointHom G x y) (g : PointHom G y z) :
    (evaluation B T).map G.t f.arrow = (evaluation B T).map G.s g.arrow := by
  sorry

/-- Composition of arrow sections is evaluation of the internal composition on
the canonical lift to the pullback of target and source. -/
def compArrow (f : PointHom G x y) (g : PointHom G y z) :
    G.R.left.obj.obj (op T) :=
  (evaluation B T).map G.c
    ((PreservesPullback.iso (evaluation B T) G.t G.s).inv
      ((Types.pullbackIsoPullback ((evaluation B T).map G.t)
        ((evaluation B T).map G.s)).inv ⟨(f.arrow, g.arrow), comp_compatible f g⟩))

/-- The composite arrow section has the source of the first arrow and the target
of the second arrow. -/
theorem comp_endpoints (f : PointHom G x y) (g : PointHom G y z) :
    G.s.left.hom.app (op T) (compArrow f g) = x ∧
    G.t.left.hom.app (op T) (compArrow f g) = z := by
  sorry

/-- Composition of successive arrows between sections. -/
def comp (f : PointHom G x y) (g : PointHom G y z) : PointHom G x z :=
  ⟨compArrow f g, (comp_endpoints f g).1, (comp_endpoints f g).2⟩

/-- Inversion interchanges the source and target of an arrow section. -/
theorem inv_endpoints (f : PointHom G x y) :
    G.s.left.hom.app (op T) (G.i.left.hom.app (op T) f.arrow) = y ∧
    G.t.left.hom.app (op T) (G.i.left.hom.app (op T) f.arrow) = x := by
  sorry

/-- The inverse of an arrow between sections. -/
def inv (f : PointHom G x y) : PointHom G y x :=
  ⟨G.i.left.hom.app (op T) f.arrow, (inv_endpoints f).1, (inv_endpoints f).2⟩

/-- Restriction of an arrow section has the restricted endpoints. -/
theorem restrict_endpoints (f : T' ⟶ T) (p : PointHom G x y) :
    G.s.left.hom.app (op T') (G.R.left.obj.map f.op p.arrow) =
      G.U.left.obj.map f.op x ∧
    G.t.left.hom.app (op T') (G.R.left.obj.map f.op p.arrow) =
      G.U.left.obj.map f.op y := by
  sorry

/-- Restriction of an arrow between sections along a site morphism. -/
def restrict (f : T' ⟶ T) (p : PointHom G x y) :
    PointHom G (G.U.left.obj.map f.op x) (G.U.left.obj.map f.op y) :=
  ⟨G.R.left.obj.map f.op p.arrow,
    (restrict_endpoints f p).1, (restrict_endpoints f p).2⟩

end PointHom

/-- Sectionwise identity, composition, and inversion satisfy the groupoid laws. -/
theorem pointGroupoid_laws (G : SheafGroupoid J B) (T : C) :
    (∀ (x y : G.U.left.obj.obj (op T)) (f : PointHom G x y),
      PointHom.comp (PointHom.id x) f = f) ∧
    (∀ (x y : G.U.left.obj.obj (op T)) (f : PointHom G x y),
      PointHom.comp f (PointHom.id y) = f) ∧
    (∀ (x y z w : G.U.left.obj.obj (op T))
        (f : PointHom G x y) (g : PointHom G y z) (h : PointHom G z w),
      PointHom.comp (PointHom.comp f g) h = PointHom.comp f (PointHom.comp g h)) ∧
    (∀ (x y : G.U.left.obj.obj (op T)) (f : PointHom G x y),
      PointHom.comp (PointHom.inv f) f = PointHom.id y) ∧
    (∀ (x y : G.U.left.obj.obj (op T)) (f : PointHom G x y),
      PointHom.comp f (PointHom.inv f) = PointHom.id x) := by
  sorry

/-- The explicit groupoid structure on sections of the object sheaf. -/
@[reducible]
def pointGroupoid (G : SheafGroupoid J B) (T : C) :
    Groupoid.{a, a} (G.U.left.obj.obj (op T)) where
  Hom := PointHom G
  id := PointHom.id
  comp := PointHom.comp
  inv := PointHom.inv
  id_comp := (pointGroupoid_laws G T).1 _ _
  comp_id := (pointGroupoid_laws G T).2.1 _ _
  assoc := (pointGroupoid_laws G T).2.2.1 _ _ _ _
  inv_comp := (pointGroupoid_laws G T).2.2.2.1 _ _
  comp_inv := (pointGroupoid_laws G T).2.2.2.2 _ _

/-- The bundled groupoid of sections over an object of the site. -/
def spacePoints (G : SheafGroupoid J B) (T : C) : Grpd.{a, a} :=
  ⟨G.U.left.obj.obj (op T), pointGroupoid G T⟩

/-- Restriction preserves sectionwise identity and composition. -/
theorem points_laws (G : SheafGroupoid J B) :
    (∀ (T T' : C) (f : T' ⟶ T) (x : G.U.left.obj.obj (op T)),
      PointHom.restrict f (PointHom.id x) =
        PointHom.id (G.U.left.obj.map f.op x)) ∧
    (∀ (T T' : C) (f : T' ⟶ T) (x y z : G.U.left.obj.obj (op T))
        (p : PointHom G x y) (q : PointHom G y z),
      PointHom.restrict f (PointHom.comp p q) =
        PointHom.comp (PointHom.restrict f p) (PointHom.restrict f q)) := by
  sorry

/-- The functor on section groupoids induced by restriction. -/
def restrict (G : SheafGroupoid J B) {T T' : C} (f : T' ⟶ T) :
    spacePoints G T ⥤ spacePoints G T' where
  obj := G.U.left.obj.map f.op
  map := PointHom.restrict f
  map_id := (points_laws G).1 T T' f
  map_comp := (points_laws G).2 T T' f _ _ _

/-- The contravariant functor of section groupoids of an internal sheaf groupoid. -/
def points (G : SheafGroupoid J B) : Cᵒᵖ ⥤ Grpd.{a, a} where
  obj T := spacePoints G T.unop
  map f := restrict G f.unop
  map_id T := by
    apply Functor.hext (F := restrict G (𝟙 T).unop)
      (G := 𝟭 (spacePoints G T.unop))
      (fun x => congrArg (fun f => f x) (G.U.left.obj.map_id T))
    intro x y p
    exact PointHom.hext _ _
      (congrArg (fun f => f x) (G.U.left.obj.map_id T))
      (congrArg (fun f => f y) (G.U.left.obj.map_id T))
      (congrArg (fun f => f p.arrow) (G.R.left.obj.map_id T))
  map_comp f g := by
    apply Functor.hext (F := restrict G (f ≫ g).unop)
      (G := restrict G f.unop ⋙ restrict G g.unop)
      (fun x => congrArg (fun h => h x) (G.U.left.obj.map_comp f g))
    intro x y p
    exact PointHom.hext _ _
      (congrArg (fun h => h x) (G.U.left.obj.map_comp f g))
      (congrArg (fun h => h y) (G.U.left.obj.map_comp f g))
      (congrArg (fun h => h p.arrow) (G.R.left.obj.map_comp f g))

section Map

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable (F : Sheaf J (Type a) ⥤ Sheaf K (Type a))
variable [PreservesFiniteLimits F] [HasPullbacks (Sheaf K (Type a))]

/-- Transported internal operations satisfy all internal groupoid equations. -/
theorem map_laws (G : SheafGroupoid J B) :
    Laws ((Over.post F).map G.s) ((Over.post F).map G.t)
      ((Over.post F).map G.e) ((Over.post F).map G.i)
      ((PreservesPullback.iso (Over.post F) G.t G.s).inv ≫
        (Over.post F).map G.c) := by
  sorry

/-- The internal groupoid obtained by applying a left-exact sheaf functor.
Composition is transported using its canonical preserved-pullback isomorphism. -/
def map (G : SheafGroupoid J B) : SheafGroupoid K (F.obj B) where
  U := (Over.post F).obj G.U
  R := (Over.post F).obj G.R
  s := (Over.post F).map G.s
  t := (Over.post F).map G.t
  e := (Over.post F).map G.e
  i := (Over.post F).map G.i
  c := (PreservesPullback.iso (Over.post F) G.t G.s).inv ≫
    (Over.post F).map G.c
  laws := map_laws F G

end Map

end SheafGroupoid

end CategoryTheory
