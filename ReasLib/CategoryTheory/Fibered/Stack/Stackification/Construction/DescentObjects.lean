module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Objects and morphisms represented by cover descent data

An object is a covering sieve with an actual descent datum. A morphism is a
descent morphism on an actual common refinement, modulo further refinement.
The constructors use sieve pullback and intersection directly, without choosing
from a stack-effectiveness or equivalence theorem.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology
open Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v uF vF

namespace CategoryTheory.Functor.StackificationConstruction.DescentCompletion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})

private def descentLaws {U : C} (R : J.Cover U)
    (obj : ∀ I : R.Arrow, F.obj (.mk (op I.Y)))
    (hom : ∀ {Y : C} (q : Y ⟶ U) {I L : R.Arrow}
      (f : Y ⟶ I.Y) (g : Y ⟶ L.Y) (_ : f ≫ I.f = q) (_ : g ≫ L.f = q),
      (F.map f.op.toLoc).toFunctor.obj (obj I) ⟶ (F.map g.op.toLoc).toFunctor.obj (obj L)) : Prop :=
  (∀ {Y' Y : C} (k : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : k ≫ q = q')
    {I L : R.Arrow} (f : Y ⟶ I.Y) (g : Y ⟶ L.Y) (hf : f ≫ I.f = q) (hg : g ≫ L.f = q)
    (kf : Y' ⟶ I.Y) (kg : Y' ⟶ L.Y) (hkf : k ≫ f = kf) (hkg : k ≫ g = kg),
    pullHom (hom q f g hf hg) k kf kg hkf hkg =
      hom q' kf kg (by rw [← hkf, Category.assoc, hf, hq])
        (by rw [← hkg, Category.assoc, hg, hq])) ∧
  (∀ {Y : C} (q : Y ⟶ U) {I : R.Arrow} (f : Y ⟶ I.Y) (hf : f ≫ I.f = q),
    hom q f f hf hf = 𝟙 _) ∧
  (∀ {Y : C} (q : Y ⟶ U) {I L M : R.Arrow}
    (f : Y ⟶ I.Y) (g : Y ⟶ L.Y) (h : Y ⟶ M.Y)
    (hf : f ≫ I.f = q) (hg : g ≫ L.f = q) (hh : h ≫ M.f = q),
    hom q f g hf hg ≫ hom q g h hg hh = hom q f h hf hh)

private def descentHomComm {U : C} {R : J.Cover U}
    (D E : F.DescentData (fun I : R.Arrow ↦ I.f)) (hom : ∀ I, D.obj I ⟶ E.obj I) : Prop :=
  ∀ {Y : C} (q : Y ⟶ U) {I L : R.Arrow} (f : Y ⟶ I.Y) (g : Y ⟶ L.Y)
    (hf : f ≫ I.f = q) (hg : g ≫ L.f = q),
    (F.map f.op.toLoc).toFunctor.map (hom I) ≫ E.hom q f g hf hg =
      D.hom q f g hf hg ≫ (F.map g.op.toLoc).toFunctor.map (hom L)

private def restrictDatumObj {U : C} {R S : J.Cover U}
    (D : F.DescentData (fun I : S.Arrow ↦ I.f)) (h : R ≤ S) (I : R.Arrow) :
    F.obj (.mk (op I.Y)) := D.obj ⟨I.Y, I.f, h I.f I.hf⟩

private def restrictDatumHom {U : C} {R S : J.Cover U}
    (D : F.DescentData (fun I : S.Arrow ↦ I.f)) (h : R ≤ S)
    {T : C} (q : T ⟶ U) {I L : R.Arrow} (k : T ⟶ I.Y) (l : T ⟶ L.Y)
    (hk : k ≫ I.f = q) (hl : l ≫ L.f = q) :
    (F.map k.op.toLoc).toFunctor.obj (restrictDatumObj J F D h I) ⟶
      (F.map l.op.toLoc).toFunctor.obj (restrictDatumObj J F D h L) :=
  D.hom q (i₁ := ⟨I.Y, I.f, h I.f I.hf⟩) (i₂ := ⟨L.Y, L.f, h L.f L.hf⟩) k l hk hl

private theorem restrictDatum_laws {U : C} {R S : J.Cover U}
    (D : F.DescentData (fun I : S.Arrow ↦ I.f)) (h : R ≤ S) :
    descentLaws J F R (restrictDatumObj J F D h) (@restrictDatumHom _ _ J F U R S D h) := sorry

/-- Restrict a descent datum to a subsieve without changing its objects or arrows. -/
def restrictDatum {U : C} {R S : J.Cover U} (D : F.DescentData (fun I : S.Arrow ↦ I.f))
    (h : R ≤ S) : F.DescentData (fun I : R.Arrow ↦ I.f) where
  obj := restrictDatumObj J F D h
  hom := fun {T} q {I L} k l hk hl ↦ restrictDatumHom J F D h q k l hk hl
  pullHom_hom := fun {Y' Y} g q q' hq {I L} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
    (restrictDatum_laws J F D h).1 g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self := fun {Y} q {I} g hg ↦ (restrictDatum_laws J F D h).2.1 q g hg
  hom_comp := fun {Y} q {I L M} f g h₃ hf hg hh ↦
    (restrictDatum_laws J F D h).2.2 q f g h₃ hf hg hh

/-- An actual cover and an actual compatible descent datum. -/
structure ObjectData (U : C) where
  /-- The covering sieve on which the data are represented. -/
  cover : J.Cover U
  /-- The descent datum on the chosen covering sieve. -/
  datum : F.DescentData (fun I : cover.Arrow ↦ I.f)

/-- A morphism represented on a specified common refinement of two covers. -/
structure RawHom {U : C} (a b : ObjectData J F U) where
  /-- The covering sieve on which the data are represented. -/
  cover : J.Cover U
  /-- The representative cover refines the source cover. -/
  left : cover ≤ a.cover
  /-- The representative cover refines the target cover. -/
  right : cover ≤ b.cover
  /-- The descent morphism on the common refinement. -/
  arrow : restrictDatum J F a.datum left ⟶ restrictDatum J F b.datum right

namespace RawHom

private theorem restrict_laws {U : C} {a b : ObjectData J F U} (φ : RawHom J F a b)
    {R : J.Cover U} (h : R ≤ φ.cover) :
    descentHomComm J F
      (restrictDatum J F a.datum (le_trans h φ.left))
      (restrictDatum J F b.datum (le_trans h φ.right))
      (fun I ↦ φ.arrow.hom ⟨I.Y, I.f, h I.f I.hf⟩) := sorry

/-- Restrict a represented descent morphism to a smaller covering sieve. -/
def restrict {U : C} {a b : ObjectData J F U} (φ : RawHom J F a b)
    {R : J.Cover U} (h : R ≤ φ.cover) : RawHom J F a b where
  cover := R
  left := le_trans h φ.left
  right := le_trans h φ.right
  arrow :=
    { hom I := φ.arrow.hom ⟨I.Y, I.f, h I.f I.hf⟩
      comm := fun {Y} q {I L} f g hf hg ↦ restrict_laws J F φ h q f g hf hg }

/-- Two represented descent morphisms agree when their arrows coincide on a
common covering refinement. -/
def Equivalent {U : C} {a b : ObjectData J F U} (φ ψ : RawHom J F a b) : Prop :=
  ∃ (R : J.Cover U) (hφ : R ≤ φ.cover) (hψ : R ≤ ψ.cover),
    (restrict J F φ hφ).arrow = (restrict J F ψ hψ).arrow

/-- Equality after common refinement is an equivalence relation. -/
theorem equivalent_equivalence {U : C} (a b : ObjectData J F U) :
    _root_.Equivalence (@Equivalent _ _ J F U a b) := sorry

private theorem id_laws {U : C} (a : ObjectData J F U) :
    descentHomComm J F (restrictDatum J F a.datum le_rfl)
      (restrictDatum J F a.datum le_rfl) (fun _ ↦ 𝟙 _) := sorry

/-- The identity representative has identity components on the original cover. -/
def id {U : C} (a : ObjectData J F U) : RawHom J F a a where
  cover := a.cover
  left := le_rfl
  right := le_rfl
  arrow := { hom _ := 𝟙 _, comm := fun {Y} q {I L} f g hf hg ↦ id_laws J F a q f g hf hg }

private theorem comp_laws {U : C} {a b c : ObjectData J F U}
    (φ : RawHom J F a b) (ψ : RawHom J F b c) :
    descentHomComm J F
      (restrictDatum J F a.datum (le_trans inf_le_left φ.left))
      (restrictDatum J F c.datum (le_trans inf_le_right ψ.right))
      (fun (I : (φ.cover ⊓ ψ.cover).Arrow) ↦
        φ.arrow.hom ⟨I.Y, I.f, I.hf.1⟩ ≫ ψ.arrow.hom ⟨I.Y, I.f, I.hf.2⟩) := sorry

/-- Composition is literal componentwise composition on the intersection of
the two representative covers. -/
def comp {U : C} {a b c : ObjectData J F U} (φ : RawHom J F a b) (ψ : RawHom J F b c) :
    RawHom J F a c where
  cover := φ.cover ⊓ ψ.cover
  left := le_trans inf_le_left φ.left
  right := le_trans inf_le_right ψ.right
  arrow :=
    { hom I := φ.arrow.hom ⟨I.Y, I.f, I.hf.1⟩ ≫ ψ.arrow.hom ⟨I.Y, I.f, I.hf.2⟩
      comm := fun {Y} q {I L} f g hf hg ↦ comp_laws J F φ ψ q f g hf hg }

/-- Componentwise composition respects common-refinement equality. -/
theorem equivalent_comp {U : C} {a b c : ObjectData J F U}
    {φ φ' : RawHom J F a b} {ψ ψ' : RawHom J F b c}
    (hφ : Equivalent J F φ φ') (hψ : Equivalent J F ψ ψ') :
    Equivalent J F (comp J F φ ψ) (comp J F φ' ψ') := sorry

/-- The equivalence relation of descent morphisms on common refinements. -/
def setoid {U : C} (a b : ObjectData J F U) : Setoid (RawHom J F a b) where
  r := Equivalent J F
  iseqv := equivalent_equivalence J F a b

end RawHom

namespace ObjectData

/-- Morphisms are classes of descent morphisms on common covering refinements. -/
def Hom {U : C} (a b : ObjectData J F U) := _root_.Quotient (RawHom.setoid J F a b)

/-- The identity class has identity components on the object's cover. -/
def id {U : C} (a : ObjectData J F U) : Hom J F a a := _root_.Quotient.mk'' (RawHom.id J F a)

/-- Composition is induced by componentwise composition on intersected covers. -/
def comp {U : C} {a b c : ObjectData J F U} (f : Hom J F a b) (g : Hom J F b c) :
    Hom J F a c :=
  _root_.Quotient.map₂ (RawHom.comp J F) (fun _ _ h _ _ k ↦ RawHom.equivalent_comp J F h k) f g

private theorem category_laws (U : C) :
    (∀ (a b : ObjectData J F U) (f : Hom J F a b), comp J F (id J F a) f = f) ∧
    (∀ (a b : ObjectData J F U) (f : Hom J F a b), comp J F f (id J F b) = f) ∧
    (∀ (a b c d : ObjectData J F U) (f : Hom J F a b) (g : Hom J F b c) (h : Hom J F c d),
      comp J F (comp J F f g) h = comp J F f (comp J F g h)) := sorry

/-- The category of cover descent data and common-refinement morphism classes. -/
@[reducible]
def category (U : C) : Category.{max u v vF} (ObjectData J F U) where
  Hom := Hom J F
  id := id J F
  comp := comp J F
  id_comp := fun f ↦ (category_laws J F U).1 _ _ f
  comp_id := fun f ↦ (category_laws J F U).2.1 _ _ f
  assoc := fun f g h ↦ (category_laws J F U).2.2 _ _ _ _ f g h

end ObjectData

/-- The bundled category of descent objects over a base object. -/
def objectCat (U : C) : Cat.{max u v vF, max u v uF vF} :=
  ⟨ObjectData J F U, ObjectData.category J F U⟩

/-- The carrier of the bundled descent-object category. -/
abbrev Object (U : C) := (objectCat J F U : Type (max u v uF vF))

/-- The category supplied by the canonical descent-object bundle. -/
@[reducible]
def objectCategory (U : C) : Category.{max u v vF} (Object J F U) := Cat.str (objectCat J F U)

private def pullbackDatumObj {U V : C} (k : V ⟶ U) (a : Object J F U)
    (I : (a.cover.pullback k).Arrow) : F.obj (.mk (op I.Y)) := a.datum.obj I.base

private def pullbackDatumHom {U V : C} (k : V ⟶ U) (a : Object J F U)
    {T : C} (q : T ⟶ V) {I L : (a.cover.pullback k).Arrow}
    (f : T ⟶ I.Y) (g : T ⟶ L.Y) (hf : f ≫ I.f = q) (hg : g ≫ L.f = q) :
    (F.map f.op.toLoc).toFunctor.obj (pullbackDatumObj J F k a I) ⟶
      (F.map g.op.toLoc).toFunctor.obj (pullbackDatumObj J F k a L) :=
  a.datum.hom (q ≫ k) (i₁ := I.base) (i₂ := L.base) f g
    ((Category.assoc f I.f k).symm.trans (congrArg (fun t ↦ t ≫ k) hf))
    ((Category.assoc g L.f k).symm.trans (congrArg (fun t ↦ t ≫ k) hg))

private theorem pullbackObject_laws {U V : C} (k : V ⟶ U) (a : Object J F U) :
    descentLaws J F (a.cover.pullback k) (pullbackDatumObj J F k a)
      (@pullbackDatumHom _ _ J F U V k a) := sorry

/-- Reindex a covering-sieve datum by composing its covering arrows with the base map. -/
def pullbackObject {U V : C} (k : V ⟶ U) (a : Object J F U) : Object J F V where
  cover := a.cover.pullback k
  datum :=
    { obj := pullbackDatumObj J F k a
      hom := fun {T} q {I L} f g hf hg ↦ pullbackDatumHom J F k a q f g hf hg
      pullHom_hom := fun {Y' Y} g q q' hq {I L} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
        (pullbackObject_laws J F k a).1 g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self := fun {Y} q {I} g hg ↦ (pullbackObject_laws J F k a).2.1 q g hg
      hom_comp := fun {Y} q {I L M} f g h hf hg hh ↦
        (pullbackObject_laws J F k a).2.2 q f g h hf hg hh }

private theorem pullbackRawHom_laws {U V : C} (k : V ⟶ U) {a b : Object J F U}
    (φ : RawHom J F a b) :
    descentHomComm J F
      (restrictDatum J F (pullbackObject J F k a).datum (fun _ _ h ↦ φ.left _ h))
      (restrictDatum J F (pullbackObject J F k b).datum (fun _ _ h ↦ φ.right _ h))
      (fun (I : (φ.cover.pullback k).Arrow) ↦ φ.arrow.hom I.base) := sorry

/-- Pull back a represented descent morphism on the pulled-back common cover. -/
def pullbackRawHom {U V : C} (k : V ⟶ U) {a b : Object J F U} (φ : RawHom J F a b) :
    RawHom J F (pullbackObject J F k a) (pullbackObject J F k b) where
  cover := φ.cover.pullback k
  left := fun _ _ h ↦ φ.left _ h
  right := fun _ _ h ↦ φ.right _ h
  arrow :=
    { hom I := φ.arrow.hom I.base
      comm := fun {Y} q {I L} f g hf hg ↦ pullbackRawHom_laws J F k φ q f g hf hg }

/-- Pullback preserves equality after common refinement. -/
theorem pullbackRawHom_respects {U V : C} (k : V ⟶ U) {a b : Object J F U}
    {φ ψ : RawHom J F a b} (h : RawHom.Equivalent J F φ ψ) :
    RawHom.Equivalent J F (pullbackRawHom J F k φ) (pullbackRawHom J F k ψ) := sorry

private def pullbackMap {U V : C} (k : V ⟶ U) {a b : Object J F U} (φ : a ⟶ b) :
    pullbackObject J F k a ⟶ pullbackObject J F k b :=
  _root_.Quotient.map (pullbackRawHom J F k) (fun _ _ h ↦ pullbackRawHom_respects J F k h) φ

private theorem pullbackFunctor_laws {U V : C} (k : V ⟶ U) :
    (∀ a : Object J F U, pullbackMap J F k (𝟙 a) = 𝟙 (pullbackObject J F k a)) ∧
    (∀ (a b c : Object J F U) (φ : a ⟶ b) (ψ : b ⟶ c),
      pullbackMap J F k (φ ≫ ψ) = pullbackMap J F k φ ≫ pullbackMap J F k ψ) := sorry

/-- Pullback acts functorially on descent objects and refinement classes. -/
def pullbackFunctor {U V : C} (k : V ⟶ U) : Object J F U ⥤ Object J F V where
  obj := pullbackObject J F k
  map := pullbackMap J F k
  map_id := (pullbackFunctor_laws J F k).1
  map_comp := fun φ ψ ↦ (pullbackFunctor_laws J F k).2 _ _ _ φ ψ

private theorem presheaf_laws :
    (∀ U : Cᵒᵖ,
      (pullbackFunctor J F (𝟙 U).unop).toCatHom = 𝟙 (Cat.of (Object J F (unop U)))) ∧
    (∀ (U V W : Cᵒᵖ) (f : U ⟶ V) (g : V ⟶ W),
      (pullbackFunctor J F (f ≫ g).unop).toCatHom =
        (pullbackFunctor J F f.unop).toCatHom ≫ (pullbackFunctor J F g.unop).toCatHom) := sorry

/-- The strict presheaf of cover descent objects and common-refinement morphisms. -/
def presheaf : Cᵒᵖ ⥤ Cat.{max u v vF, max u v uF vF} where
  obj U := Cat.of (Object J F (unop U))
  map k := (pullbackFunctor J F k.unop).toCatHom
  map_id := (presheaf_laws J F).1
  map_comp := fun f g ↦ (presheaf_laws J F).2 _ _ _ f g

/-- The singleton/maximal-cover comparison on every original fibre category. -/
def ofObject {U : C} (x : F.obj (.mk (op U))) : Object J F U where
  cover := ⊤
  datum := Pseudofunctor.DescentData.ofObj x

private theorem unitFunctor_map_comm {U : C} {x y : F.obj (.mk (op U))} (φ : x ⟶ y) :
    descentHomComm J F
      (restrictDatum J F (ofObject J F x).datum le_rfl)
      (restrictDatum J F (ofObject J F y).datum le_rfl)
      (fun (I : (⊤ : J.Cover U).Arrow) ↦ (F.map I.f.op.toLoc).toFunctor.map φ) := sorry

private def unitRawHom {U : C} {x y : F.obj (.mk (op U))} (φ : x ⟶ y) :
    RawHom J F (ofObject J F x) (ofObject J F y) where
  cover := ⊤
  left := le_rfl
  right := le_rfl
  arrow :=
    { hom I := (F.map I.f.op.toLoc).toFunctor.map φ
      comm := fun {Y} q {I L} f g hf hg ↦ unitFunctor_map_comm J F φ q f g hf hg }

private def unitMap {U : C} {x y : F.obj (.mk (op U))} (φ : x ⟶ y) :
    ofObject J F x ⟶ ofObject J F y := _root_.Quotient.mk'' (unitRawHom J F φ)

private theorem unitFunctor_laws (U : C) :
    (∀ x : F.obj (.mk (op U)), unitMap J F (𝟙 x) = 𝟙 (ofObject J F x)) ∧
    (∀ (x y z : F.obj (.mk (op U))) (φ : x ⟶ y) (ψ : y ⟶ z),
      unitMap J F (φ ≫ ψ) = unitMap J F φ ≫ unitMap J F ψ) := sorry

/-- The maximal-cover comparison from each original fibre into its descent completion. -/
def unitFunctor (U : C) : F.obj (.mk (op U)) ⥤ Object J F U where
  obj := ofObject J F
  map := unitMap J F
  map_id := (unitFunctor_laws J F U).1
  map_comp := fun φ ψ ↦ (unitFunctor_laws J F U).2 _ _ _ φ ψ

end CategoryTheory.Functor.StackificationConstruction.DescentCompletion
