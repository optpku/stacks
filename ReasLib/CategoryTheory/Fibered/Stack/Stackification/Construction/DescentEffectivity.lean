/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.DescentHom
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Flattening a descent datum of cover descent objects

The outer cover and each supplied object's stored cover determine the bound
cover. Transition arrows are read from actual representatives of the supplied
descent morphisms. Native coherence maps of the original pseudofunctor place
them in the original Hom presheaf before amalgamation.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology

noncomputable section

universe u v uF vF

namespace CategoryTheory.Functor.StackificationConstruction.DescentCompletion.ObjectGluing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})
variable {U : C} (R : J.Cover U)
variable (D : (presheaf J F).toPseudofunctor'.DescentData
  (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom))

/-- The supplied local cover-descent object at an outer covering arrow. -/
def localObject (I : R.Arrow) : Object J F I.Y :=
  D.obj (Presieve.categoryMk (R : Sieve U).arrows I.f I.hf)

/-- The actual bound cover obtained from the covers stored by local objects. -/
def cover : J.Cover U :=
  R.bind fun I ↦ (localObject J F R D I).cover

/-- An explicit inner covering arrow together with its outer covering arrow.
Keeping this index explicit also describes pieces whose chosen bind
factorization uses a different original outer member. -/
structure Index where
  outer : R.Arrow
  inner : (localObject J F R D outer).cover.Arrow

namespace Index

def Y (I : Index J F R D) : C := I.inner.Y

def f (I : Index J F R D) : I.Y ⟶ U := I.inner.f ≫ I.outer.f

def ofBound (K : (cover J F R D).Arrow) : Index J F R D :=
  ⟨K.fromMiddle, K.toMiddle⟩

theorem middle_spec (I : Index J F R D) : I.inner.f ≫ I.outer.f = I.f := rfl

end Index

/-- An object of the original pseudofunctor on every arrow of the bound cover. -/
def piece (K : Index J F R D) : F.obj (.mk (op K.Y)) :=
  (localObject J F R D K.outer).datum.obj K.inner

/-- A supplied transition has a native quotient representative on the test
object. Its raw cover, component objects and maps are all original input data. -/
def transitionRepresentative {T : C} (q : T ⟶ U) {K L : Index J F R D}
    (f : T ⟶ K.Y) (g : T ⟶ L.Y) (hf : f ≫ K.f = q) (hg : g ≫ L.f = q) :
    RawHom J F
      (pullbackObject J F (f ≫ K.inner.f) (localObject J F R D K.outer))
      (pullbackObject J F (g ≫ L.inner.f) (localObject J F R D L.outer)) :=
  _root_.Quotient.out
    (D.hom q
      (i₁ := Presieve.categoryMk (R : Sieve U).arrows K.outer.f K.outer.hf)
      (i₂ := Presieve.categoryMk (R : Sieve U).arrows L.outer.f L.outer.hf)
      (f ≫ K.inner.f) (g ≫ L.inner.f)
      ((Category.assoc f K.inner.f K.outer.f).trans
        ((congrArg (fun t ↦ f ≫ t) K.middle_spec).trans hf))
      ((Category.assoc g L.inner.f L.outer.f).trans
        ((congrArg (fun t ↦ g ≫ t) L.middle_spec).trans hg)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A transition component in the original Hom presheaf. Its maps are the
stored raw arrow, original descent transitions, and original pseudofunctor unit
and composition maps, with no chosen equivalence or effectiveness witness. -/
def localTransition {T : C} (q : T ⟶ U) {K L : Index J F R D}
    (f : T ⟶ K.Y) (g : T ⟶ L.Y) (hf : f ≫ K.f = q) (hg : g ≫ L.f = q)
    (I : (transitionRepresentative J F R D q f g hf hg).cover.Arrow) :
    (F.map I.f.op.toLoc).toFunctor.obj
        ((F.map f.op.toLoc).toFunctor.obj (piece J F R D K)) ⟶
      (F.map I.f.op.toLoc).toFunctor.obj
        ((F.map g.op.toLoc).toFunctor.obj (piece J F R D L)) := by
  let a := localObject J F R D K.outer
  let b := localObject J F R D L.outer
  let raw := transitionRepresentative J F R D q f g hf hg
  let ia : a.cover.Arrow := ⟨I.Y, I.f ≫ (f ≫ K.inner.f), raw.left I.f I.hf⟩
  let ib : b.cover.Arrow := ⟨I.Y, I.f ≫ (g ≫ L.inner.f), raw.right I.f I.hf⟩
  let leftBridge := a.datum.hom (I.f ≫ (f ≫ K.inner.f))
    (i₁ := K.inner) (i₂ := ia) (I.f ≫ f) (𝟙 I.Y)
    (Category.assoc I.f f K.inner.f) (Category.id_comp _)
  let rightBridge := b.datum.hom (I.f ≫ (g ≫ L.inner.f))
    (i₁ := ib) (i₂ := L.inner) (𝟙 I.Y) (I.f ≫ g)
    (Category.id_comp _) (Category.assoc I.f g L.inner.f)
  exact (F.mapComp' f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc rfl).inv.toNatTrans.app
      (piece J F R D K) ≫
    leftBridge ≫ (F.mapId (.mk (op I.Y))).hom.toNatTrans.app (a.datum.obj ia) ≫
      raw.arrow.hom I ≫ (F.mapId (.mk (op I.Y))).inv.toNatTrans.app (b.datum.obj ib) ≫
        rightBridge ≫
          (F.mapComp' g.op.toLoc I.f.op.toLoc (I.f ≫ g).op.toLoc rfl).hom.toNatTrans.app
            (piece J F R D L)

/-- The original prestack condition globalizes the local representative
compatibilities. It is explicit in this matching-family law. -/
theorem localTransition_compatible (hF : F.IsPrestack J)
    {T : C} (q : T ⟶ U) {K L : Index J F R D}
    (f : T ⟶ K.Y) (g : T ⟶ L.Y) (hf : f ≫ K.f = q) (hg : g ≫ L.f = q) :
    Presieve.Arrows.Compatible
      (F.presheafHom ((F.map f.op.toLoc).toFunctor.obj (piece J F R D K))
        ((F.map g.op.toLoc).toFunctor.obj (piece J F R D L)))
      (X := fun I : (transitionRepresentative J F R D q f g hf hg).cover.Arrow ↦ Over.mk I.f)
      (B := Over.mk (𝟙 T)) (fun I ↦ Over.homMk I.f (Category.comp_id I.f))
      (fun I ↦ localTransition J F R D q f g hf hg I) := sorry

/-- The global transition is the original Hom sheaf amalgamation of actual
local components, obtained from the supplied original prestack data. -/
def transition (hF : F.IsPrestack J)
    {T : C} (q : T ⟶ U) {K L : Index J F R D}
    (f : T ⟶ K.Y) (g : T ⟶ L.Y) (hf : f ≫ K.f = q) (hg : g ≫ L.f = q) :
    (F.map f.op.toLoc).toFunctor.obj (piece J F R D K) ⟶
      (F.map g.op.toLoc).toFunctor.obj (piece J F R D L) := by
  let raw := transitionRepresentative J F R D q f g hf hg
  let x := (F.map f.op.toLoc).toFunctor.obj (piece J F R D K)
  let y := (F.map g.op.toLoc).toFunctor.obj (piece J F R D L)
  let family := fun I : raw.cover.Arrow ↦ I.f
  let localHom : (F.toDescentData family).obj x ⟶ (F.toDescentData family).obj y :=
    Pseudofunctor.DescentData.subtypeCompatibleHomEquiv F family
      ⟨fun I ↦ localTransition J F R D q f g hf hg I,
        localTransition_compatible J F R D hF q f g hf hg⟩
  have covering : Sieve.ofArrows (fun I : raw.cover.Arrow ↦ I.Y) family ∈ J T := by
    apply J.superset_covering ?_ raw.cover.condition
    intro V k hk
    exact Sieve.ofArrows_mk (fun I : raw.cover.Arrow ↦ I.Y) family (⟨V, k, hk⟩ : raw.cover.Arrow)
  letI : F.IsPrestack J := hF
  exact (F.fullyFaithfulToDescentData family covering).preimage localHom

/-- The explicit transitions respect restriction along test arrows. -/
theorem transition_pullHom (hF : F.IsPrestack J)
    {T' T : C} (k : T' ⟶ T) (q : T ⟶ U) (q' : T' ⟶ U) (hq : k ≫ q = q')
    {I L : Index J F R D} (f : T ⟶ I.Y) (g : T ⟶ L.Y)
    (hf : f ≫ I.f = q) (hg : g ≫ L.f = q)
    (kf : T' ⟶ I.Y) (kg : T' ⟶ L.Y) (hkf : k ≫ f = kf) (hkg : k ≫ g = kg) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (transition J F R D hF q f g hf hg) k kf kg hkf hkg =
      transition J F R D hF q' kf kg
        (by rw [← hkf, Category.assoc, hf, hq])
        (by rw [← hkg, Category.assoc, hg, hq]) := sorry

/-- The explicit self-transition is the identity. -/
theorem transition_self (hF : F.IsPrestack J)
    {T : C} (q : T ⟶ U) {I : Index J F R D}
    (f : T ⟶ I.Y) (hf : f ≫ I.f = q) :
    transition J F R D hF q f f hf hf = 𝟙 _ := sorry

/-- The explicit transitions satisfy the cocycle law. -/
theorem transition_comp (hF : F.IsPrestack J)
    {T : C} (q : T ⟶ U) {I L M : Index J F R D}
    (f : T ⟶ I.Y) (g : T ⟶ L.Y) (h : T ⟶ M.Y)
    (hf : f ≫ I.f = q) (hg : g ≫ L.f = q) (hh : h ≫ M.f = q) :
    transition J F R D hF q f g hf hg ≫ transition J F R D hF q g h hg hh =
      transition J F R D hF q f h hf hh := sorry

/-- The actual flattened object stores the bound cover, its actual original
objects, and the actual amalgamated transitions. -/
def object (hF : F.IsPrestack J) : Object J F U where
  cover := cover J F R D
  datum :=
    { obj K := piece J F R D (Index.ofBound J F R D K)
      hom := fun {T} q {I L} f g hf hg ↦
        transition J F R D hF q (K := Index.ofBound J F R D I)
          (L := Index.ofBound J F R D L) f g
          ((congrArg (fun t ↦ f ≫ t) I.middle_spec).trans hf)
          ((congrArg (fun t ↦ g ≫ t) L.middle_spec).trans hg)
      pullHom_hom := by
        intro T' T k q q' hq I L f g hf hg kf kg hkf hkg
        exact transition_pullHom J F R D hF k q q' hq
          (I := Index.ofBound J F R D I) (L := Index.ofBound J F R D L) f g
          ((congrArg (fun t ↦ f ≫ t) I.middle_spec).trans hf)
          ((congrArg (fun t ↦ g ≫ t) L.middle_spec).trans hg) kf kg hkf hkg
      hom_self := by
        intro T q I f hf
        exact transition_self J F R D hF q (I := Index.ofBound J F R D I) f
          ((congrArg (fun t ↦ f ≫ t) I.middle_spec).trans hf)
      hom_comp := by
        intro T q I L M f g h hf hg hh
        exact transition_comp J F R D hF q
          (I := Index.ofBound J F R D I) (L := Index.ofBound J F R D L)
          (M := Index.ofBound J F R D M) f g h
          ((congrArg (fun t ↦ f ≫ t) I.middle_spec).trans hf)
          ((congrArg (fun t ↦ g ≫ t) L.middle_spec).trans hg)
          ((congrArg (fun t ↦ h ≫ t) M.middle_spec).trans hh) }

/-- The comparison of the global object with an original local object uses an
actual common refinement of their stored covers. -/
def comparisonCover (I : R.Arrow) : J.Cover I.Y :=
  (cover J F R D).pullback I.f ⊓ (localObject J F R D I).cover

/-- Forward local comparison, using the global transition between the actual
bound-cover piece and the explicitly retained original local piece. -/
def comparisonRaw (hF : F.IsPrestack J) (I : R.Arrow) :
    RawHom J F (pullbackObject J F I.f (object J F R D hF)) (localObject J F R D I) where
  cover := comparisonCover J F R D I
  left := inf_le_left
  right := inf_le_right
  arrow :=
    { hom K := by
        let bound : (cover J F R D).Arrow := ⟨K.Y, K.f ≫ I.f, K.hf.1⟩
        let left := Index.ofBound J F R D bound
        let right : Index J F R D := ⟨I, ⟨K.Y, K.f, K.hf.2⟩⟩
        exact (F.mapId (.mk (op K.Y))).inv.toNatTrans.app (piece J F R D left) ≫
          transition J F R D hF (K.f ≫ I.f) (K := left) (L := right) (𝟙 K.Y) (𝟙 K.Y)
            ((Category.id_comp left.f).trans bound.middle_spec) (Category.id_comp right.f) ≫
              (F.mapId (.mk (op K.Y))).hom.toNatTrans.app (piece J F R D right)
      comm := by sorry }

/-- The inverse local comparison uses the reverse actual transition, with the
same common cover and the native unit maps in the reverse order. -/
def comparisonInverseRaw (hF : F.IsPrestack J) (I : R.Arrow) :
    RawHom J F (localObject J F R D I) (pullbackObject J F I.f (object J F R D hF)) where
  cover := comparisonCover J F R D I
  left := inf_le_right
  right := inf_le_left
  arrow :=
    { hom K := by
        let bound : (cover J F R D).Arrow := ⟨K.Y, K.f ≫ I.f, K.hf.1⟩
        let left := Index.ofBound J F R D bound
        let right : Index J F R D := ⟨I, ⟨K.Y, K.f, K.hf.2⟩⟩
        exact (F.mapId (.mk (op K.Y))).inv.toNatTrans.app (piece J F R D right) ≫
          transition J F R D hF (K.f ≫ I.f) (K := right) (L := left) (𝟙 K.Y) (𝟙 K.Y)
            (Category.id_comp right.f) ((Category.id_comp left.f).trans bound.middle_spec) ≫
              (F.mapId (.mk (op K.Y))).hom.toNatTrans.app (piece J F R D left)
      comm := by sorry }

/-- Both directions of the local comparison are explicit quotient classes;
only the inverse laws are postponed. -/
def comparisonIso (hF : F.IsPrestack J) (I : R.Arrow) :
    pullbackObject J F I.f (object J F R D hF) ≅ localObject J F R D I where
  hom := _root_.Quotient.mk'' (comparisonRaw J F R D hF I)
  inv := _root_.Quotient.mk'' (comparisonInverseRaw J F R D hF I)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The comparison with the supplied descent datum has the actual local
comparison and actual inverse as its components. -/
def glueIso (hF : F.IsPrestack J) :
    ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj (object J F R D hF) ≅ D where
  hom :=
    { hom I := (comparisonIso J F R D hF ⟨I.obj.left, I.obj.hom, I.property⟩).hom
      comm := by sorry }
  inv :=
    { hom I := (comparisonIso J F R D hF ⟨I.obj.left, I.obj.hom, I.property⟩).inv
      comm := by sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The native stack condition stores the actual global object and actual
comparison isomorphism for each supplied covering-sieve datum. -/
theorem isStack (hF : F.IsPrestack J) : (presheaf J F).toPseudofunctor'.IsStack J where
  toIsPrestack := DescentCompletion.isPrestack J F hF
  essSurj_of_sieve R hR :=
    { mem_essImage := fun D ↦
        ⟨object J F ⟨R, hR⟩ D hF, ⟨glueIso J F ⟨R, hR⟩ D hF⟩⟩ }

end CategoryTheory.Functor.StackificationConstruction.DescentCompletion.ObjectGluing
