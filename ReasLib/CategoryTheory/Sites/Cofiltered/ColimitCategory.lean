module

public import ReasLib.CategoryTheory.Sites.Cofiltered.Basic

/-!
# Explicit colimit categories of cofiltered site diagrams

This file owns the categorical colimit model attached to a
`CofilteredSiteDiagram`.  It is deliberately independent of the generated
colimit topology and of Chapter 7: the carrier is the quotient of stage
objects by common lowering, and its morphisms are the corresponding quotient
of stage morphisms.  The site-level construction belongs in a layer importing
this one.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe uI uC vC

namespace CategoryTheory

namespace CofilteredSiteDiagram

variable (S : CofilteredSiteDiagram.{uI, uC, vC})

section TransitionCalculus

/-- A cospan in the cofiltered indexing category admits a commuting common lowering. -/
theorem exists_span {j k₁ k₂ : S.I} (f : k₁ ⟶ j) (g : k₂ ⟶ j) :
    ∃ (m : S.I) (u : m ⟶ k₁) (v : m ⟶ k₂), u ≫ f = v ≫ g := sorry

/-- Object-level composition for the transition functors of a cofiltered site diagram. -/
theorem stageFunctor_obj_comp {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) (X : S.stage i) :
    (S.stageFunctor b).obj ((S.stageFunctor a).obj X) =
      (S.stageFunctor (b ≫ a)).obj X := sorry

/-- Object-level identity for the transition functors of a cofiltered site diagram. -/
theorem stageFunctor_obj_id {i : S.I} (X : S.stage i) :
    (S.stageFunctor (𝟙 i)).obj X = X := sorry

/-- Morphism-level composition for transition functors, with canonical object transports. -/
theorem stageFunctor_map_map {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageFunctor b).map ((S.stageFunctor a).map f) =
      eqToHom (S.stageFunctor_obj_comp a b X) ≫ (S.stageFunctor (b ≫ a)).map f ≫
        eqToHom (S.stageFunctor_obj_comp a b Y).symm := sorry

/-- Morphism-level identity for transition functors, with canonical object transports. -/
theorem stageFunctor_map_id {i : S.I} {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageFunctor (𝟙 i)).map f =
      eqToHom (S.stageFunctor_obj_id X) ≫ f ≫ eqToHom (S.stageFunctor_obj_id Y).symm := sorry

/-- Arrow-level transition composition, avoiding endpoint transport bookkeeping. -/
theorem arrowMk_map_map {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    {X Y : S.stage i} (f : X ⟶ Y) :
    Arrow.mk ((S.stageFunctor b).map ((S.stageFunctor a).map f)) =
      Arrow.mk ((S.stageFunctor (b ≫ a)).map f) := sorry

/-- Arrow-level transition identity, avoiding endpoint transport bookkeeping. -/
theorem arrowMk_map_id {i : S.I} {X Y : S.stage i} (f : X ⟶ Y) :
    Arrow.mk ((S.stageFunctor (𝟙 i)).map f) = Arrow.mk f := sorry

end TransitionCalculus

section ArrowCalculus

variable {C : Type*} [Category C]

/-- Equality of `Arrow.mk` values is exactly equality of endpoints and the transported arrow. -/
theorem arrowMk_eq_iff {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    Arrow.mk f = Arrow.mk g ↔
      ∃ (h₁ : X₁ = X₂) (h₂ : Y₁ = Y₂),
        f = eqToHom h₁ ≫ g ≫ eqToHom h₂.symm := sorry

/-- Precomposing by an endpoint transport does not change an arrow's `Arrow.mk` class. -/
theorem arrowMk_eqToHom_comp {X X' Y : C} (h : X' = X) (f : X ⟶ Y) :
    Arrow.mk (eqToHom h ≫ f) = Arrow.mk f := sorry

/-- Postcomposing by an endpoint transport does not change an arrow's `Arrow.mk` class. -/
theorem arrowMk_comp_eqToHom {X Y Y' : C} (f : X ⟶ Y) (h : Y = Y') :
    Arrow.mk (f ≫ eqToHom h) = Arrow.mk f := sorry

/-- Transport-compatible arrow equalities can be pasted horizontally. -/
theorem arrowMk_glue_comp_congr {X₁ Y₁ X₂ Y₂ Z₁ W₁ Z₂ W₂ : C}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {g₁ : Z₁ ⟶ W₁} {g₂ : Z₂ ⟶ W₂}
    (hf : Arrow.mk f₁ = Arrow.mk f₂) (hg : Arrow.mk g₁ = Arrow.mk g₂)
    (h₁ : Y₁ = Z₁) (h₂ : Y₂ = Z₂) :
    Arrow.mk (f₁ ≫ eqToHom h₁ ≫ g₁) = Arrow.mk (f₂ ≫ eqToHom h₂ ≫ g₂) := sorry

/-- Parallel arrows with equal `Arrow.mk` values are equal. -/
theorem eq_of_arrowMk_eq {X Y : C} {u v : X ⟶ Y}
    (h : Arrow.mk u = Arrow.mk v) : u = v := sorry

end ArrowCalculus

section Objects

/-- A raw object representative in a cofiltered colimit category. -/
structure ObjRep where
  /-- The index of the stage presenting the object. -/
  idx : S.I
  /-- The object at that stage. -/
  obj : S.stage idx

/-- Object representatives are equivalent when they become equal after a common lowering. -/
def objRel (p q : S.ObjRep) : Prop :=
  ∃ (k : S.I) (a : k ⟶ p.idx) (b : k ⟶ q.idx),
    (S.stageFunctor a).obj p.obj = (S.stageFunctor b).obj q.obj

/-- Common lowering relates an object representative to itself. -/
theorem objRel_refl (p : S.ObjRep) : S.objRel p p := sorry

/-- Common lowering is symmetric on object representatives. -/
theorem objRel_symm {p q : S.ObjRep} (h : S.objRel p q) : S.objRel q p := sorry

/-- Common lowering is transitive on object representatives. -/
theorem objRel_trans {p q r : S.ObjRep} (h₁ : S.objRel p q) (h₂ : S.objRel q r) :
    S.objRel p r := sorry

/-- The setoid of object representatives under common lowering. -/
instance objSetoid : Setoid (S.ObjRep) :=
  ⟨S.objRel, S.objRel_refl, S.objRel_symm, S.objRel_trans⟩

/-- Lemma 7.18.2 (09YL): the explicit colimit category's objects are stage objects modulo
common lowering. -/
@[stacks 09YL]
def ColimitCategory : Type max uI uC :=
  _root_.Quotient S.objSetoid

/-- The canonical image of a stage object in the explicit colimit category. -/
def ιObj (i : S.I) (X : S.stage i) : S.ColimitCategory :=
  _root_.Quotient.mk _ ⟨i, X⟩

/-- Lowering a stage object preserves its image in the colimit category. -/
theorem ιObj_lower {i k : S.I} (a : k ⟶ i) (X : S.stage i) :
    S.ιObj k ((S.stageFunctor a).obj X) = S.ιObj i X := sorry

/-- Every colimit object has a stage presentation. -/
theorem ιObj_surjective (x : S.ColimitCategory) :
    ∃ (i : S.I) (X : S.stage i), S.ιObj i X = x := sorry

/-- Equal stage presentations agree after a common lowering. -/
theorem ιObj_exact {i j : S.I} {X : S.stage i} {Y : S.stage j}
    (h : S.ιObj i X = S.ιObj j Y) :
    ∃ (k : S.I) (a : k ⟶ i) (b : k ⟶ j),
      (S.stageFunctor a).obj X = (S.stageFunctor b).obj Y := sorry

end Objects

section Homs

variable {S}

/-- A raw morphism representative between two objects of the explicit colimit category. -/
structure HomRep (x y : S.ColimitCategory) where
  /-- The index of the presenting stage. -/
  idx : S.I
  /-- The presenting source object. -/
  src : S.stage idx
  /-- The presenting target object. -/
  tgt : S.stage idx
  /-- The presenting stage morphism. -/
  hom : src ⟶ tgt
  /-- The source presentation. -/
  hsrc : S.ιObj idx src = x
  /-- The target presentation. -/
  htgt : S.ιObj idx tgt = y

/-- Morphism representatives are equivalent when their lowerings have equal arrow images. -/
def homRel {x y : S.ColimitCategory} (r₁ r₂ : HomRep x y) : Prop :=
  ∃ (k : S.I) (a : k ⟶ r₁.idx) (b : k ⟶ r₂.idx),
    Arrow.mk ((S.stageFunctor a).map r₁.hom) = Arrow.mk ((S.stageFunctor b).map r₂.hom)

/-- Common lowering relates a morphism representative to itself. -/
theorem homRel_refl {x y : S.ColimitCategory} (r : HomRep x y) : homRel r r := sorry

/-- Common lowering is symmetric on morphism representatives. -/
theorem homRel_symm {x y : S.ColimitCategory} {r₁ r₂ : HomRep x y}
    (h : homRel r₁ r₂) : homRel r₂ r₁ := sorry

/-- Common lowering is transitive on morphism representatives. -/
theorem homRel_trans {x y : S.ColimitCategory} {r₁ r₂ r₃ : HomRep x y}
    (h₁ : homRel r₁ r₂) (h₂ : homRel r₂ r₃) : homRel r₁ r₃ := sorry

/-- The setoid of morphism representatives between two fixed colimit objects. -/
instance homSetoid (x y : S.ColimitCategory) : Setoid (HomRep x y) :=
  ⟨homRel, homRel_refl, homRel_symm, homRel_trans⟩

/-- Lower a morphism representative along a transition arrow. -/
def HomRep.lower {x y : S.ColimitCategory} (r : HomRep x y) {k : S.I} (a : k ⟶ r.idx) :
    HomRep x y :=
  ⟨k, (S.stageFunctor a).obj r.src, (S.stageFunctor a).obj r.tgt,
    (S.stageFunctor a).map r.hom, (S.ιObj_lower a r.src).trans r.hsrc,
    (S.ιObj_lower a r.tgt).trans r.htgt⟩

/-- A lowered morphism representative is equivalent to its original representative. -/
theorem HomRep.lower_rel {x y : S.ColimitCategory} (r : HomRep x y) {k : S.I}
    (a : k ⟶ r.idx) : homRel (r.lower a) r := sorry

end Homs

section Composition

variable {S}

/-- Data for composing two stage morphism representatives after lowering their middle objects. -/
structure CompData {x y z : S.ColimitCategory} (r : HomRep x y) (s : HomRep y z) where
  /-- The common lower stage. -/
  idx : S.I
  /-- The lowering map for the first representative. -/
  toFst : idx ⟶ r.idx
  /-- The lowering map for the second representative. -/
  toSnd : idx ⟶ s.idx
  /-- The identification of the lowered middle objects. -/
  glue : (S.stageFunctor toFst).obj r.tgt = (S.stageFunctor toSnd).obj s.src

/-- A canonical choice of composition data, obtained from the equality of the middle
colimit presentations. -/
noncomputable def CompData.some {x y z : S.ColimitCategory} (r : HomRep x y)
    (s : HomRep y z) : CompData r s :=
  let h : ∃ (k : S.I) (a : k ⟶ r.idx) (b : k ⟶ s.idx),
      (S.stageFunctor a).obj r.tgt = (S.stageFunctor b).obj s.src :=
    _root_.Quotient.exact (r.htgt.trans s.hsrc.symm)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

/-- The explicit composite represented by composition data. -/
def CompData.comp {x y z : S.ColimitCategory} {r : HomRep x y} {s : HomRep y z}
    (d : CompData r s) : HomRep x z :=
  ⟨d.idx, (S.stageFunctor d.toFst).obj r.src, (S.stageFunctor d.toSnd).obj s.tgt,
    (S.stageFunctor d.toFst).map r.hom ≫ eqToHom d.glue ≫ (S.stageFunctor d.toSnd).map s.hom,
    (S.ιObj_lower d.toFst r.src).trans r.hsrc,
    (S.ιObj_lower d.toSnd s.tgt).trans s.htgt⟩

/-- Lowered composites have the expected three-factor arrow form. -/
theorem CompData.arrowMk_lower_comp {x y z : S.ColimitCategory} {r : HomRep x y}
    {s : HomRep y z} (d : CompData r s) {n : S.I} (w : n ⟶ d.idx) :
    Arrow.mk ((S.stageFunctor w).map d.comp.hom) =
      Arrow.mk ((S.stageFunctor (w ≫ d.toFst)).map r.hom ≫
        eqToHom ((S.stageFunctor_obj_comp d.toFst w r.tgt).symm.trans
          ((congrArg (S.stageFunctor w).obj d.glue).trans
            (S.stageFunctor_obj_comp d.toSnd w s.src))) ≫
        (S.stageFunctor (w ≫ d.toSnd)).map s.hom) := sorry

/-- Different choices of composition data yield equivalent representatives. -/
theorem CompData.comp_rel {x y z : S.ColimitCategory} {r : HomRep x y} {s : HomRep y z}
    (d d' : CompData r s) : homRel d.comp d'.comp := sorry

/-- Replacing the first representative by an equivalent one preserves composite classes. -/
theorem CompData.comp_rel_left {x y z : S.ColimitCategory} {r₁ r₂ : HomRep x y}
    {s : HomRep y z} (h : homRel r₁ r₂) (d₂ : CompData r₂ s) :
    ∃ (d₁ : CompData r₁ s), homRel d₁.comp d₂.comp := sorry

/-- Replacing the second representative by an equivalent one preserves composite classes. -/
theorem CompData.comp_rel_right {x y z : S.ColimitCategory} {r : HomRep x y}
    {s₁ s₂ : HomRep y z} (h : homRel s₁ s₂) (d₂ : CompData r s₂) :
    ∃ (d₁ : CompData r s₁), homRel d₁.comp d₂.comp := sorry

/-- Composition of representative classes is independent of all representative choices. -/
theorem CompData.comp_sound {x y z : S.ColimitCategory} {r₁ r₂ : HomRep x y}
    {s₁ s₂ : HomRep y z} (hr : homRel r₁ r₂) (hs : homRel s₁ s₂)
    (d₁ : CompData r₁ s₁) (d₂ : CompData r₂ s₂) :
    homRel d₁.comp d₂.comp := sorry

/-- Associativity holds on common-lowering classes of representatives. -/
theorem CompData.assoc_rel {w x y z : S.ColimitCategory} (r : HomRep w x) (s : HomRep x y)
    (t : HomRep y z) :
    homRel (CompData.some (CompData.some r s).comp t).comp
      (CompData.some r (CompData.some s t).comp).comp := sorry

end Composition

section CategoryInstance

variable {S}

/-- The representative chosen for the identity of a colimit object. -/
noncomputable def idRep (x : S.ColimitCategory) : HomRep x x :=
  ⟨(_root_.Quotient.exists_rep x).choose.idx, (_root_.Quotient.exists_rep x).choose.obj,
    (_root_.Quotient.exists_rep x).choose.obj, 𝟙 (_root_.Quotient.exists_rep x).choose.obj,
    (_root_.Quotient.exists_rep x).choose_spec, (_root_.Quotient.exists_rep x).choose_spec⟩

/-- Identity-shaped representatives of the same colimit object are equivalent. -/
theorem homRel_id_id {x : S.ColimitCategory} {p q : S.ObjRep}
    (hp : S.ιObj p.idx p.obj = x) (hq : S.ιObj q.idx q.obj = x) :
    homRel (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp⟩ : HomRep x x)
      ⟨q.idx, q.obj, q.obj, 𝟙 q.obj, hq, hq⟩ := sorry

/-- Right composition with an identity-shaped representative preserves the morphism class. -/
theorem CompData.comp_id_rel {x y : S.ColimitCategory} {r : HomRep x y} {q : S.ObjRep}
    {hq : S.ιObj q.idx q.obj = y}
    (d : CompData r (⟨q.idx, q.obj, q.obj, 𝟙 q.obj, hq, hq⟩ : HomRep y y)) :
    homRel d.comp r := sorry

/-- Left composition with an identity-shaped representative preserves the morphism class. -/
theorem CompData.id_comp_rel {x y : S.ColimitCategory} {r : HomRep x y} {p : S.ObjRep}
    {hp : S.ιObj p.idx p.obj = x}
    (d : CompData (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp⟩ : HomRep x x) r) :
    homRel d.comp r := sorry

variable (S)

/-- The category structure on the explicit common-lowering quotient. -/
noncomputable instance instCategoryColimitCategory :
    Category.{max uI uC vC} S.ColimitCategory where
  Hom x y := _root_.Quotient (homSetoid x y)
  id x := _root_.Quotient.mk _ (idRep x)
  comp {x y z} f g :=
    _root_.Quotient.lift₂
      (fun (r : HomRep x y) (s : HomRep y z) =>
        (_root_.Quotient.mk _ (CompData.some r s).comp : _root_.Quotient (homSetoid x z)))
      (fun r₁ s₁ r₂ s₂ hr hs =>
        _root_.Quotient.sound
          (CompData.comp_sound hr hs (CompData.some r₁ s₁) (CompData.some r₂ s₂)))
      f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end CategoryInstance

section Interface

variable {S}

/-- Morphisms of the colimit category are quotient classes exactly when their representatives
are related by common lowering. -/
theorem hom_mk_eq_iff {x y : S.ColimitCategory} (r₁ r₂ : HomRep x y) :
    (_root_.Quotient.mk _ r₁ : x ⟶ y) = _root_.Quotient.mk _ r₂ ↔ homRel r₁ r₂ := sorry

/-- Composition of two representative classes is the class attached to any composition datum. -/
theorem mk_comp_mk {x y z : S.ColimitCategory} (r : HomRep x y) (s : HomRep y z)
    (d : CompData r s) :
    (_root_.Quotient.mk _ r ≫ _root_.Quotient.mk _ s : x ⟶ z) =
      _root_.Quotient.mk _ d.comp := sorry

/-- The identity of a colimit object is represented by any presentation of that object. -/
theorem id_eq_mk {x : S.ColimitCategory} (p : S.ObjRep) (hp : S.ιObj p.idx p.obj = x) :
    (𝟙 x : x ⟶ x) =
      _root_.Quotient.mk _ (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp⟩ : HomRep x x) := sorry

/-- A transport between colimit objects is represented by an identity at any source presentation. -/
theorem eqToHom_eq_mk {x y : S.ColimitCategory} (h : x = y) (p : S.ObjRep)
    (hp : S.ιObj p.idx p.obj = x) :
    eqToHom h =
      (_root_.Quotient.mk _ (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp.trans h⟩ : HomRep x y) :
        x ⟶ y) := sorry

end Interface

section Cocone

/-- The canonical cocone functor from one stage into the explicit colimit category. -/
noncomputable def stageCoconeFunctor (i : S.I) : S.stage i ⥤ S.ColimitCategory where
  obj X := S.ιObj i X
  map f := _root_.Quotient.mk _ ⟨i, _, _, f, rfl, rfl⟩
  map_id := sorry
  map_comp := sorry

/-- The cocone functors are compatible with the transition functors. -/
theorem stageCoconeFunctor_comp_eq {i j : S.I} (a : j ⟶ i) :
    S.stageFunctor a ⋙ S.stageCoconeFunctor j = S.stageCoconeFunctor i := sorry

end Cocone

section Descent

variable {S}

/-- Every colimit morphism between stage images is represented after a common lowering. -/
theorem exists_hom_rep {i j : S.I} {X : S.stage i} {Y : S.stage j}
    (f : S.ιObj i X ⟶ S.ιObj j Y) :
    ∃ (k : S.I) (a : k ⟶ i) (b : k ⟶ j)
      (g : (S.stageFunctor a).obj X ⟶ (S.stageFunctor b).obj Y),
      f = _root_.Quotient.mk _ ⟨k, (S.stageFunctor a).obj X, (S.stageFunctor b).obj Y, g,
        S.ιObj_lower a X, S.ιObj_lower b Y⟩ := sorry

/-- Equal cocone images of parallel stage morphisms become equal after a common lowering. -/
theorem exists_stageFunctor_map_eq {i : S.I} {X Y : S.stage i} {f g : X ⟶ Y}
    (h : (S.stageCoconeFunctor i).map f = (S.stageCoconeFunctor i).map g) :
    ∃ (k : S.I) (a : k ⟶ i), (S.stageFunctor a).map f = (S.stageFunctor a).map g := sorry

/-- Every colimit object is in the essential image of a stage cocone functor. -/
theorem stageCoconeFunctor_obj_surjective (x : S.ColimitCategory) :
    ∃ (i : S.I) (X : S.stage i), (S.stageCoconeFunctor i).obj X = x := sorry

/-- The cocone image of a stage morphism is its defining representative class. -/
theorem stageCoconeFunctor_map_eq {i : S.I} {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageCoconeFunctor i).map f =
      _root_.Quotient.mk _ ⟨i, X, Y, f, rfl, rfl⟩ := sorry

/-- An arbitrarily transported representative class is the corresponding transported cocone map. -/
theorem mk_eq_eqToHom_comp {x y : S.ColimitCategory} {k : S.I} {A B : S.stage k}
    (g : A ⟶ B) (hA : S.ιObj k A = x) (hB : S.ιObj k B = y) :
    (_root_.Quotient.mk _ (⟨k, A, B, g, hA, hB⟩ : HomRep x y) : x ⟶ y) =
      eqToHom hA.symm ≫ (S.stageCoconeFunctor k).map g ≫ eqToHom hB := sorry

/-- Lowering a stage morphism conjugates its image under the cocone functor. -/
theorem stageCoconeFunctor_map_lower {i k : S.I} (a : k ⟶ i) {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageCoconeFunctor i).map f =
      eqToHom (S.ιObj_lower a X).symm ≫
        (S.stageCoconeFunctor k).map ((S.stageFunctor a).map f) ≫
        eqToHom (S.ιObj_lower a Y) := sorry

/-- Lowering a stage morphism preserves its `Arrow.mk` image under the cocone. -/
theorem arrowMk_cocone_map_lower {i k : S.I} (a : k ⟶ i) {X Y : S.stage i} (f : X ⟶ Y) :
    Arrow.mk ((S.stageCoconeFunctor i).map f) =
      Arrow.mk ((S.stageCoconeFunctor k).map ((S.stageFunctor a).map f)) := sorry

/-- A stage morphism whose cocone image is invertible becomes invertible after a common lowering. -/
theorem exists_stageFunctor_map_isIso {i : S.I} {X Y : S.stage i} (g : X ⟶ Y)
    [IsIso ((S.stageCoconeFunctor i).map g)] :
    ∃ (k : S.I) (a : k ⟶ i), IsIso ((S.stageFunctor a).map g) := sorry

/-- Two colimit morphisms from a common stage image admit simultaneous stage representatives. -/
theorem exists_hom_rep_pair {i₀ i : S.I} {X : S.stage i₀} {Y₁ Y₂ : S.stage i}
    (f₁ : S.ιObj i₀ X ⟶ S.ιObj i Y₁) (f₂ : S.ιObj i₀ X ⟶ S.ιObj i Y₂) :
    ∃ (k : S.I) (a : k ⟶ i₀) (b : k ⟶ i)
      (g₁ : (S.stageFunctor a).obj X ⟶ (S.stageFunctor b).obj Y₁)
      (g₂ : (S.stageFunctor a).obj X ⟶ (S.stageFunctor b).obj Y₂),
      f₁ = eqToHom (S.ιObj_lower a X).symm ≫ (S.stageCoconeFunctor k).map g₁ ≫
        eqToHom (S.ιObj_lower b Y₁) ∧
      f₂ = eqToHom (S.ιObj_lower a X).symm ≫ (S.stageCoconeFunctor k).map g₂ ≫
        eqToHom (S.ιObj_lower b Y₂) := sorry

/-- An equality after one lowering remains an equality after further lowering. -/
theorem stageFunctor_map_eq_lower {k : S.I} {A B : S.stage k} {x y : A ⟶ B}
    {n : S.I} (δ : n ⟶ k) {n' : S.I} (w : n' ⟶ n)
    (h : (S.stageFunctor δ).map x = (S.stageFunctor δ).map y) :
    (S.stageFunctor (w ≫ δ)).map x = (S.stageFunctor (w ≫ δ)).map y := sorry

end Descent

end CofilteredSiteDiagram

end CategoryTheory
