/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.LocalEquality

/-!
# Compatible local morphisms in the separated stage

The morphism carrier is a covering sieve together with original quotient arrows
from every reindexed source and their compatibility under further restriction.
Composition uses the original native cover binding and its actual factorization.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory GrothendieckTopology

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

/-- The actual original object restricted along a covering arrow. -/
def sourceRestriction (a : Separated J p χ) {T : C} (k : T ⟶ p.obj a.obj) : X :=
  (χ.reindexObj k (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))).1

/-- The original Cartesian arrow comparing a two-step restriction with a
one-step restriction; its quotient class is used in matching-family conditions. -/
def refinementArrow (a : Separated J p χ) {T T' : C} (k : T ⟶ p.obj a.obj) (l : T' ⟶ T) :
    sourceRestriction J p χ a (l ≫ k) ⟶ sourceRestriction J p χ a k := by
  let first := χ.reindexLift k (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))
  let second := χ.reindexLift (l ≫ k) (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))
  exact @Functor.IsStronglyCartesian.map C X _ _ p T (p.obj a.obj)
    first.source a.obj k first.hom first.isStronglyCartesian T' second.source l (l ≫ k)
    rfl second.hom second.isStronglyCartesian.toIsHomLift

/-- The original refinement map retains its displayed base arrow. -/
theorem refinementArrow_isHomLift (a : Separated J p χ) {T T' : C}
    (k : T ⟶ p.obj a.obj) (l : T' ⟶ T) :
    p.IsHomLift l (refinementArrow J p χ a k l) := by
  let first := χ.reindexLift k (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))
  let second := χ.reindexLift (l ≫ k) (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))
  exact @Functor.IsStronglyCartesian.map_isHomLift C X _ _ p T (p.obj a.obj)
    first.source a.obj k first.hom first.isStronglyCartesian
    T' second.source l (l ≫ k) rfl second.hom second.isStronglyCartesian.toIsHomLift

private theorem refinementArrow_fac (a : Separated J p χ) {T T' : C}
    (k : T ⟶ p.obj a.obj) (l : T' ⟶ T) :
    refinementArrow J p χ a k l ≫ χ.cartesianHom k (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj)) =
      χ.cartesianHom (l ≫ k) (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj)) := by
  let first := χ.reindexLift k (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))
  let second := χ.reindexLift (l ≫ k) (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))
  exact @Functor.IsStronglyCartesian.fac C X _ _ p T (p.obj a.obj)
    first.source a.obj k first.hom first.isStronglyCartesian T' second.source l (l ≫ k)
    rfl second.hom second.isStronglyCartesian.toIsHomLift

private theorem separated_map_isHomLift {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    (hφ : p.IsHomLift f φ) :
    (Separated.projection J p χ).IsHomLift f ((Separated.ofOriginal J p χ).map φ) := by
  cases hφ
  exact CategoryTheory.IsHomLift.map (Separated.projection J p χ)
    ((Separated.ofOriginal J p χ).map φ)

private theorem separated_cartesianHom_congr (a : Separated J p χ) {T : C}
    {f g : T ⟶ p.obj a.obj} (h : f = g) :
    eqToHom (congrArg ((Separated.ofOriginal J p χ).obj ∘ sourceRestriction J p χ a) h) ≫
        (Separated.ofOriginal J p χ).map
          (χ.cartesianHom g (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))) =
      (Separated.ofOriginal J p χ).map
        (χ.cartesianHom f (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))) := by
  cases h
  exact Category.id_comp _

/-- A compatible family of local arrows with a fixed base arrow. -/
structure LocalArrow (a b : Separated J p χ) where
  /-- The common base arrow of the local components. -/
  base : p.obj a.obj ⟶ p.obj b.obj
  /-- The covering sieve on which the components are given. -/
  cover : J.Cover (p.obj a.obj)
  /-- The component from the Cartesian restriction along a covering arrow. -/
  component (I : cover.Arrow) :
    (Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a I.f) ⟶ b
  /-- Each component lies over the restriction of the common base arrow. -/
  isHomLift (I : cover.Arrow) :
    (Separated.projection J p χ).IsHomLift (I.f ≫ base) (component I)
  /-- Components agree under further Cartesian restriction. -/
  compatibility (I : cover.Arrow) {T : C} (k : T ⟶ I.Y) :
    (Separated.ofOriginal J p χ).map (refinementArrow J p χ a I.f k) ≫ component I =
      component (I.precomp k)

namespace LocalArrow

private def ofSeparatedComponent {a b : Separated J p χ} (φ : a ⟶ b)
    (I : (⊤ : J.Cover (p.obj a.obj)).Arrow) :
    (Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a I.f) ⟶ b :=
  (Separated.ofOriginal J p χ).map
    (χ.cartesianHom I.f (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))) ≫ φ

private theorem ofSeparated_laws {a b : Separated J p χ} (φ : a ⟶ b) :
    (∀ I : (⊤ : J.Cover (p.obj a.obj)).Arrow,
      (Separated.projection J p χ).IsHomLift
        (I.f ≫ (Separated.projection J p χ).map φ) (ofSeparatedComponent J p χ φ I)) ∧
    (∀ (I : (⊤ : J.Cover (p.obj a.obj)).Arrow) {T : C} (k : T ⟶ I.Y),
      (Separated.ofOriginal J p χ).map (refinementArrow J p χ a I.f k) ≫
        ofSeparatedComponent J p χ φ I = ofSeparatedComponent J p χ φ (I.precomp k)) := by
  constructor
  · intro I
    have h : (Separated.projection J p χ).IsHomLift I.f
        ((Separated.ofOriginal J p χ).map
          (χ.cartesianHom I.f (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj)))) :=
      separated_map_isHomLift J p χ _ _
        (χ.reindexLift I.f (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))).isStronglyCartesian.toIsHomLift
    exact @IsHomLift.comp _ _ _ _ (Separated.projection J p χ) _ _ _ _ _ _ _ _ _ _ h
      (.map φ)
  · intro I T k
    dsimp only [ofSeparatedComponent]
    rw [← Category.assoc, ← Functor.map_comp, refinementArrow_fac]
    rfl

/-- A separated arrow becomes the matching family on the maximal cover. -/
def ofSeparated {a b : Separated J p χ} (φ : a ⟶ b) : LocalArrow J p χ a b where
  base := (Separated.projection J p χ).map φ
  cover := ⊤
  component := ofSeparatedComponent J p χ φ
  isHomLift := (ofSeparated_laws J p χ φ).1
  compatibility := (ofSeparated_laws J p χ φ).2

/-- The actual factor of one local component into the original reindexed
target, obtained from its stored quotient Cartesian witness. -/
def toTargetRestriction {a b : Separated J p χ} (φ : LocalArrow J p χ a b)
    (I : φ.cover.Arrow) :
    (Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a I.f) ⟶
      (Separated.ofOriginal J p χ).obj (sourceRestriction J p χ b (I.f ≫ φ.base)) := by
  let target := χ.reindexLift (I.f ≫ φ.base) (⟨b.obj, rfl⟩ : p.Fiber (p.obj b.obj))
  let strong := @Separated.mapIsStronglyCartesian _ _ _ _ J p χ
    target.source b.obj _ _ (I.f ≫ φ.base) target.hom target.isStronglyCartesian
  let cartesian : (Separated.projection J p χ).IsCartesian (I.f ≫ φ.base)
      ((Separated.ofOriginal J p χ).map target.hom) :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      C (Separated J p χ) _ _ (Separated.projection J p χ) _ _
      ((Separated.ofOriginal J p χ).obj target.source) b
      (I.f ≫ φ.base) ((Separated.ofOriginal J p χ).map target.hom) strong
  exact @Functor.IsCartesian.map C (Separated J p χ) _ _ (Separated.projection J p χ)
    I.Y (p.obj b.obj) ((Separated.ofOriginal J p χ).obj target.source) b
    (I.f ≫ φ.base) ((Separated.ofOriginal J p χ).map target.hom) cartesian
    ((Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a I.f)) (φ.component I) (φ.isHomLift I)

private def compComponent {a b c : Separated J p χ} (φ : LocalArrow J p χ a b)
    (ψ : LocalArrow J p χ b c)
    (K : (φ.cover.bind (fun I ↦ ψ.cover.pullback (I.f ≫ φ.base))).Arrow) :
    (Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a K.f) ⟶ c := by
  let I := K.fromMiddle
  let L := K.toMiddle
  let h := K.toMiddleHom
  let target := χ.reindexLift L.base.f (⟨b.obj, rfl⟩ : p.Fiber (p.obj b.obj))
  let strong := @Separated.mapIsStronglyCartesian _ _ _ _ J p χ
    target.source b.obj _ _ L.base.f target.hom target.isStronglyCartesian
  let cartesian : (Separated.projection J p χ).IsCartesian L.base.f
      ((Separated.ofOriginal J p χ).map target.hom) :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      C (Separated J p χ) _ _ (Separated.projection J p χ) _ _
      ((Separated.ofOriginal J p χ).obj target.source) b
      L.base.f ((Separated.ofOriginal J p χ).map target.hom) strong
  let numerator := (Separated.ofOriginal J p χ).map
    (refinementArrow J p χ a I.f h) ≫ φ.component I
  let numerator_lift : (Separated.projection J p χ).IsHomLift L.base.f numerator := by
    have h_ref : p.IsHomLift h (refinementArrow J p χ a I.f h) :=
      refinementArrow_isHomLift J p χ a I.f h
    have h_ref' : (Separated.projection J p χ).IsHomLift h
        ((Separated.ofOriginal J p χ).map (refinementArrow J p χ a I.f h)) :=
      @BasedFunctor.preserves_isHomLift C _ (BasedCategory.ofFunctor p)
        (BasedCategory.ofFunctor (Separated.projection J p χ))
        (Separated.comparison J p χ).toBasedFunctor K.Y I.Y
        (sourceRestriction J p χ a (h ≫ I.f)) (sourceRestriction J p χ a I.f)
        h (refinementArrow J p χ a I.f h) h_ref
    have h_comp : (Separated.projection J p χ).IsHomLift
        (h ≫ (I.f ≫ φ.base)) numerator :=
      @IsHomLift.comp C (Separated J p χ) _ _ (Separated.projection J p χ)
        K.Y I.Y (p.obj b.obj)
        ((Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a (h ≫ I.f)))
        ((Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a I.f)) b
        h (I.f ≫ φ.base)
        ((Separated.ofOriginal J p χ).map (refinementArrow J p χ a I.f h))
        (φ.component I) h_ref' (φ.isHomLift I)
    have base_eq : h ≫ (I.f ≫ φ.base) = L.base.f := by
      rfl
    exact base_eq ▸ h_comp
  let factorArrow := @Functor.IsCartesian.map C (Separated J p χ) _ _
    (Separated.projection J p χ) K.Y (p.obj b.obj)
    ((Separated.ofOriginal J p χ).obj target.source) b L.base.f
    ((Separated.ofOriginal J p χ).map target.hom) cartesian
    ((Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a (h ≫ I.f))) numerator numerator_lift
  exact eqToHom (congrArg ((Separated.ofOriginal J p χ).obj ∘ sourceRestriction J p χ a)
    K.middle_spec.symm) ≫ factorArrow ≫ ψ.component L.base

set_option backward.isDefEq.respectTransparency false in
private theorem comp_ofSeparatedComponent {a b c : Separated J p χ} (f : a ⟶ b) (g : b ⟶ c)
    (K : ((ofSeparated J p χ f).cover.bind
      (fun I ↦ (ofSeparated J p χ g).cover.pullback (I.f ≫ (ofSeparated J p χ f).base))).Arrow) :
    compComponent J p χ (ofSeparated J p χ f) (ofSeparated J p χ g) K =
      (Separated.ofOriginal J p χ).map
        (χ.cartesianHom K.f (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))) ≫ (f ≫ g) := by
  let target := χ.reindexLift K.toMiddle.base.f (⟨b.obj, rfl⟩ : p.Fiber (p.obj b.obj))
  letI := @Separated.mapIsStronglyCartesian _ _ _ _ J p χ
    target.source b.obj _ _ K.toMiddle.base.f target.hom target.isStronglyCartesian
  letI := separated_map_isHomLift J p χ K.toMiddleHom
    (refinementArrow J p χ a K.fromMiddle.f K.toMiddleHom)
    (refinementArrow_isHomLift J p χ a K.fromMiddle.f K.toMiddleHom)
  letI := (ofSeparated J p χ f).isHomLift K.fromMiddle
  letI : (Separated.projection J p χ).IsHomLift K.toMiddle.base.f
      ((Separated.ofOriginal J p χ).map (refinementArrow J p χ a K.fromMiddle.f K.toMiddleHom) ≫
        (ofSeparated J p χ f).component K.fromMiddle) :=
    CategoryTheory.IsHomLift.comp (Separated.projection J p χ) K.toMiddleHom
      (K.fromMiddle.f ≫ (ofSeparated J p χ f).base) _ _
  simp only [compComponent, ofSeparated, ofSeparatedComponent, Functor.Cleavage.cartesianHom,
    Category.assoc, Functor.IsCartesian.fac_assoc]
  have hfac := refinementArrow_fac J p χ a K.fromMiddle.f K.toMiddleHom
  dsimp only [Functor.Cleavage.cartesianHom] at hfac
  rw [← Functor.map_comp_assoc, hfac]
  have hcongr := separated_cartesianHom_congr J p χ a K.middle_spec.symm
  dsimp only [Functor.Cleavage.cartesianHom] at hcongr
  simpa only [Category.assoc, Cover.Arrow.fromMiddle, Function.comp_apply] using
    congrArg (fun t ↦ t ≫ (f ≫ g)) hcongr

private theorem comp_laws {a b c : Separated J p χ} (φ : LocalArrow J p χ a b)
    (ψ : LocalArrow J p χ b c) :
    (∀ K : (φ.cover.bind (fun I ↦ ψ.cover.pullback (I.f ≫ φ.base))).Arrow,
      (Separated.projection J p χ).IsHomLift (K.f ≫ (φ.base ≫ ψ.base))
        (compComponent J p χ φ ψ K)) ∧
    (∀ (I : (φ.cover.bind (fun I ↦ ψ.cover.pullback (I.f ≫ φ.base))).Arrow)
      {T : C} (k : T ⟶ I.Y),
      (Separated.ofOriginal J p χ).map (refinementArrow J p χ a I.f k) ≫
        compComponent J p χ φ ψ I = compComponent J p χ φ ψ (I.precomp k)) := sorry

/-- Compose local arrows on the bound cover using their Cartesian factors. -/
def comp {a b c : Separated J p χ} (φ : LocalArrow J p χ a b)
    (ψ : LocalArrow J p χ b c) : LocalArrow J p χ a c where
  base := φ.base ≫ ψ.base
  cover := φ.cover.bind (fun I ↦ ψ.cover.pullback (I.f ≫ φ.base))
  component := compComponent J p χ φ ψ
  isHomLift := (comp_laws J p χ φ ψ).1
  compatibility := (comp_laws J p χ φ ψ).2

end LocalArrow

namespace LocalArrow

/-- Two local arrows agree when their base arrows and all their restrictions
to common refinements agree in the separated category. -/
def Equivalent {a b : Separated J p χ} (φ ψ : LocalArrow J p χ a b) : Prop :=
  φ.base = ψ.base ∧ ∀ (I : φ.cover.Arrow) (L : ψ.cover.Arrow) {T : C}
    (k : T ⟶ I.Y) (l : T ⟶ L.Y) (h : k ≫ I.f = l ≫ L.f),
    (Separated.ofOriginal J p χ).map (refinementArrow J p χ a I.f k) ≫ φ.component I =
      eqToHom (congrArg ((Separated.ofOriginal J p χ).obj ∘ sourceRestriction J p χ a) h) ≫
        (Separated.ofOriginal J p χ).map (refinementArrow J p χ a L.f l) ≫ ψ.component L

/-- Agreement on common refinements is an equivalence relation. -/
theorem equivalent_equivalence (a b : Separated J p χ) :
    _root_.Equivalence (@Equivalent _ _ _ _ J p χ a b) := sorry

/-- Composition preserves agreement on common refinements. -/
theorem equivalent_comp {a b c : Separated J p χ}
    {φ φ' : LocalArrow J p χ a b} {ψ ψ' : LocalArrow J p χ b c}
    (hφ : Equivalent J p χ φ φ') (hψ : Equivalent J p χ ψ ψ') :
    Equivalent J p χ (comp J p χ φ ψ) (comp J p χ φ' ψ') := sorry

/-- Local arrows modulo agreement on common refinements. -/
def setoid (a b : Separated J p χ) : Setoid (LocalArrow J p χ a b) where
  r := Equivalent J p χ
  iseqv := equivalent_equivalence J p χ a b

end LocalArrow

/-- The local-morphism stage retains an original object in its separated form. -/
structure LocalizedData (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage) where
  /-- The underlying separated object. -/
  obj : Separated J p χ

namespace LocalizedData

/-- Arrows are compatible local families modulo common-refinement equality. -/
def Hom (a b : LocalizedData J p χ) := Quotient (LocalArrow.setoid J p χ a.obj b.obj)

/-- The identity is represented by the identity on the maximal cover. -/
def id (a : LocalizedData J p χ) : Hom J p χ a a :=
  Quotient.mk'' (LocalArrow.ofSeparated J p χ (𝟙 a.obj))

/-- Composition is induced by the bound-cover composition of representatives. -/
def comp {a b c : LocalizedData J p χ} (f : Hom J p χ a b) (g : Hom J p χ b c) :
    Hom J p χ a c :=
  Quotient.map₂ (LocalArrow.comp J p χ)
    (fun _ _ h _ _ k ↦ LocalArrow.equivalent_comp J p χ h k) f g

private theorem category_laws :
    (∀ (a b : LocalizedData J p χ) (f : Hom J p χ a b), comp J p χ (id J p χ a) f = f) ∧
    (∀ (a b : LocalizedData J p χ) (f : Hom J p χ a b), comp J p χ f (id J p χ b) = f) ∧
    (∀ (a b c d : LocalizedData J p χ) (f : Hom J p χ a b) (g : Hom J p χ b c)
      (h : Hom J p χ c d), comp J p χ (comp J p χ f g) h = comp J p χ f (comp J p χ g h)) := sorry

/-- The category of original objects with compatible local morphisms. -/
@[reducible]
def category : Category.{max u v vX} (LocalizedData J p χ) where
  Hom := Hom J p χ
  id := id J p χ
  comp := comp J p χ
  id_comp := fun f ↦ (category_laws J p χ).1 _ _ f
  comp_id := fun f ↦ (category_laws J p χ).2.1 _ _ f
  assoc := fun f g h ↦ (category_laws J p χ).2.2 _ _ _ _ f g h

end LocalizedData

/-- The bundled category of original objects and local-arrow classes. -/
def localizedCategory : Cat.{max u v vX, uX} :=
  ⟨LocalizedData J p χ, LocalizedData.category J p χ⟩

/-- The carrier of the local-morphism category. -/
abbrev Localized := (localizedCategory J p χ : Type uX)

namespace Localized

/-- The category supplied by the canonical local-morphism bundle. -/
@[reducible]
def category : Category.{max u v vX} (Localized J p χ) := Cat.str (localizedCategory J p χ)

private def projectionMap {a b : Localized J p χ} (f : a ⟶ b) : p.obj a.obj.obj ⟶ p.obj b.obj.obj :=
  Quotient.lift (fun (φ : LocalArrow J p χ a.obj b.obj) ↦ φ.base)
    (fun _ _ (h : LocalArrow.Equivalent J p χ _ _) ↦ h.1) f

private theorem projection_laws :
    (∀ a : Localized J p χ, projectionMap J p χ (𝟙 a) = 𝟙 (p.obj a.obj.obj)) ∧
    (∀ (a b c : Localized J p χ) (f : a ⟶ b) (g : b ⟶ c),
      projectionMap J p χ (f ≫ g) = projectionMap J p χ f ≫ projectionMap J p χ g) := by
  constructor
  · intro a
    exact p.map_id a.obj.obj
  · intro a b c f g
    exact Quotient.inductionOn₂ f g (fun _ _ ↦ rfl)

/-- Projection evaluates the stored base arrow of a local-arrow class. -/
def projection : Localized J p χ ⥤ C where
  obj a := p.obj a.obj.obj
  map := projectionMap J p χ
  map_id := (projection_laws J p χ).1
  map_comp := fun f g ↦ (projection_laws J p χ).2 _ _ _ f g

private def fromSeparatedMap {a b : Separated J p χ} (φ : a ⟶ b) :
    LocalizedData.Hom J p χ ⟨a⟩ ⟨b⟩ :=
  Quotient.mk'' (LocalArrow.ofSeparated J p χ φ)

set_option backward.isDefEq.respectTransparency false in
private theorem fromSeparated_laws :
    ∀ (a b c : Separated J p χ) (f : a ⟶ b) (g : b ⟶ c),
      fromSeparatedMap J p χ (f ≫ g) =
        LocalizedData.comp J p χ (fromSeparatedMap J p χ f) (fromSeparatedMap J p χ g) := by
  intro a b c f g
  apply Quotient.sound
  constructor
  · exact (Separated.projection J p χ).map_comp f g
  · intro I L T k l h
    change (Separated.ofOriginal J p χ).map (refinementArrow J p χ a I.f k) ≫
        ((Separated.ofOriginal J p χ).map
          (χ.cartesianHom I.f (⟨a.obj, rfl⟩ : p.Fiber (p.obj a.obj))) ≫ (f ≫ g)) =
      eqToHom (congrArg ((Separated.ofOriginal J p χ).obj ∘ sourceRestriction J p χ a) h) ≫
        (Separated.ofOriginal J p χ).map (refinementArrow J p χ a L.f l) ≫
          LocalArrow.compComponent J p χ (LocalArrow.ofSeparated J p χ f)
            (LocalArrow.ofSeparated J p χ g) L
    rw [LocalArrow.comp_ofSeparatedComponent, ← Functor.map_comp_assoc,
      refinementArrow_fac J p χ a I.f k, ← Functor.map_comp_assoc,
      refinementArrow_fac J p χ a L.f l]
    simpa only [Category.assoc] using
      (congrArg (fun t ↦ t ≫ (f ≫ g)) (separated_cartesianHom_congr J p χ a h)).symm

/-- A separated morphism gives its local-arrow class on the maximal cover. -/
def fromSeparated : Separated J p χ ⥤ Localized J p χ where
  obj a := ⟨a⟩
  map := fromSeparatedMap J p χ
  map_id := fun _ ↦ rfl
  map_comp := fun f g ↦ fromSeparated_laws J p χ _ _ _ f g

/-- Original arrows map to their maximal-cover local-arrow classes. -/
def fromOriginal : X ⥤ Localized J p χ :=
  Separated.ofOriginal J p χ ⋙ fromSeparated J p χ

/-- A quotient-arrow representative retains the same displayed base arrow. -/
theorem representative_base {a b : Localized J p χ} (τ : a ⟶ b) :
    (Quotient.out τ).base = (projection J p χ).map τ := by
  exact congrArg (projectionMap J p χ) (Quotient.out_eq τ)

private theorem rawFactor_piece_isHomLift {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] {c : Separated J p χ}
    (numerator : LocalArrow J p χ c ((Separated.ofOriginal J p χ).obj b))
    (I : numerator.cover.Arrow) :
    (Separated.projection J p χ).IsHomLift
      (I.f ≫ numerator.base ≫ eqToHom (@IsHomLift.codomain_eq C X _ _ p R S a b f φ hφ.toIsHomLift))
      (numerator.component I) := by
  simpa only [Category.assoc] using
    (IsHomLift.lift_comp_eqToHom_iff (Separated.projection J p χ)
      (I.f ≫ numerator.base) (numerator.component I)
      (@IsHomLift.codomain_eq C X _ _ p R S a b f φ hφ.toIsHomLift)).2
        (numerator.isHomLift I)

private def rawFactorComponent {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] {c : Localized J p χ} (k : p.obj c.obj.obj ⟶ R)
    (τ : c ⟶ (fromOriginal J p χ).obj b) [hτ : (projection J p χ).IsHomLift (k ≫ f) τ]
    (I : (Quotient.out τ).cover.Arrow) :
    (Separated.ofOriginal J p χ).obj (sourceRestriction J p χ c.obj I.f) ⟶
      (Separated.ofOriginal J p χ).obj a := by
  let numerator : LocalArrow J p χ c.obj ((Separated.ofOriginal J p χ).obj b) := Quotient.out τ
  let target := (Separated.ofOriginal J p χ).map φ
  let strong := Separated.mapIsStronglyCartesian J p χ f φ
  let endpoint := @IsHomLift.codomain_eq C X _ _ p R S a b f φ
    (inferInstance : p.IsStronglyCartesian f φ).toIsHomLift
  have native_eq : (projection J p χ).map τ ≫ eqToHom endpoint = k ≫ f := by
    simpa only [projection, fromOriginal, fromSeparated, Separated.ofOriginal,
      Functor.comp_obj, eqToHom_refl, Category.id_comp] using
      (@IsHomLift.fac C (Localized J p χ) _ _ (projection J p χ)
        (p.obj c.obj.obj) S c ((fromOriginal J p χ).obj b) (k ≫ f) τ hτ).symm
  have base_eq : numerator.base ≫ eqToHom endpoint = k ≫ f :=
    (congrArg (fun r : p.obj c.obj.obj ⟶ p.obj b ↦ r ≫ eqToHom endpoint)
      (representative_base J p χ τ)).trans native_eq
  let piece := numerator.component I
  let piece_lift : (Separated.projection J p χ).IsHomLift
      (I.f ≫ numerator.base ≫ eqToHom (@IsHomLift.codomain_eq C X _ _ p R S a b f φ (inferInstance : p.IsStronglyCartesian f φ).toIsHomLift)) piece := rawFactor_piece_isHomLift J p χ f φ numerator I
  exact @Functor.IsStronglyCartesian.map C (Separated J p χ) _ _
    (Separated.projection J p χ) R S
    ((Separated.ofOriginal J p χ).obj a) ((Separated.ofOriginal J p χ).obj b)
    f target strong I.Y ((Separated.ofOriginal J p χ).obj (sourceRestriction J p χ c.obj I.f))
    (I.f ≫ k) (I.f ≫ numerator.base ≫ eqToHom (@IsHomLift.codomain_eq C X _ _ p R S a b f φ (inferInstance : p.IsStronglyCartesian f φ).toIsHomLift))
    (by simpa only [Category.assoc] using congrArg (fun r ↦ I.f ≫ r) base_eq) piece piece_lift

private theorem rawFactorComponent_isHomLift {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] {c : Localized J p χ} (k : p.obj c.obj.obj ⟶ R)
    (τ : c ⟶ (fromOriginal J p χ).obj b) [(projection J p χ).IsHomLift (k ≫ f) τ]
    (I : (Quotient.out τ).cover.Arrow) :
    (Separated.projection J p χ).IsHomLift (I.f ≫ k)
      (rawFactorComponent J p χ f φ k τ I) := by
  letI := Separated.mapIsStronglyCartesian J p χ f φ
  letI := rawFactor_piece_isHomLift J p χ f φ (Quotient.out τ) I
  dsimp only [rawFactorComponent]
  exact Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _

private theorem rawFactorComponent_fac {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] {c : Localized J p χ} (k : p.obj c.obj.obj ⟶ R)
    (τ : c ⟶ (fromOriginal J p χ).obj b) [(projection J p χ).IsHomLift (k ≫ f) τ]
    (I : (Quotient.out τ).cover.Arrow) :
    rawFactorComponent J p χ f φ k τ I ≫ (Separated.ofOriginal J p χ).map φ =
      (Quotient.out τ).component I := by
  letI := Separated.mapIsStronglyCartesian J p χ f φ
  letI := rawFactor_piece_isHomLift J p χ f φ (Quotient.out τ) I
  dsimp only [rawFactorComponent]
  exact Functor.IsStronglyCartesian.fac _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem rawFactor_laws {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] {c : Localized J p χ} (k : p.obj c.obj.obj ⟶ R)
    (τ : c ⟶ (fromOriginal J p χ).obj b) [hτ : (projection J p χ).IsHomLift (k ≫ f) τ] :
    (∀ I : (Quotient.out τ).cover.Arrow,
      (Separated.projection J p χ).IsHomLift (I.f ≫ (k ≫ eqToHom (@IsHomLift.domain_eq C X _ _ p R S a b f φ hφ.toIsHomLift).symm))
        (rawFactorComponent J p χ f φ k τ I)) ∧
    (∀ (I : (Quotient.out τ).cover.Arrow) {T : C} (l : T ⟶ I.Y),
      (Separated.ofOriginal J p χ).map (refinementArrow J p χ c.obj I.f l) ≫
        rawFactorComponent J p χ f φ k τ I = rawFactorComponent J p χ f φ k τ (I.precomp l)) := by
  constructor
  · intro I
    simpa only [Category.assoc] using
      (IsHomLift.lift_comp_eqToHom_iff (Separated.projection J p χ)
        (I.f ≫ k) (rawFactorComponent J p χ f φ k τ I)
        (@IsHomLift.domain_eq C X _ _ p R S a b f φ hφ.toIsHomLift).symm).2
          (rawFactorComponent_isHomLift J p χ f φ k τ I)
  · intro I T l
    letI := Separated.mapIsStronglyCartesian J p χ f φ
    letI := rawFactorComponent_isHomLift J p χ f φ k τ I
    letI := separated_map_isHomLift J p χ l (refinementArrow J p χ c.obj I.f l)
      (refinementArrow_isHomLift J p χ c.obj I.f l)
    letI : (Separated.projection J p χ).IsHomLift (l ≫ (I.f ≫ k))
        (rawFactorComponent J p χ f φ k τ (I.precomp l)) := by
      have h := rawFactorComponent_isHomLift J p χ f φ k τ (I.precomp l)
      exact (Category.assoc l I.f k) ▸ h
    apply Functor.IsStronglyCartesian.ext (Separated.projection J p χ) f
      ((Separated.ofOriginal J p χ).map φ) (l ≫ (I.f ≫ k))
    rw [Category.assoc, rawFactorComponent_fac J p χ f φ k τ I,
      rawFactorComponent_fac J p χ f φ k τ (I.precomp l)]
    exact (Quotient.out τ).compatibility I l

/-- Factor each stored local component through the original Cartesian lift,
retaining the representative cover and its explicit factor arrows. -/
def rawFactor {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] {c : Localized J p χ} (k : p.obj c.obj.obj ⟶ R)
    (τ : c ⟶ (fromOriginal J p χ).obj b) [hτ : (projection J p χ).IsHomLift (k ≫ f) τ] :
    LocalArrow J p χ c.obj ((Separated.ofOriginal J p χ).obj a) where
  base := k ≫ eqToHom (@IsHomLift.domain_eq C X _ _ p R S a b f φ hφ.toIsHomLift).symm
  cover := (Quotient.out τ).cover
  component := rawFactorComponent J p χ f φ k τ
  isHomLift := (rawFactor_laws J p χ f φ k τ).1
  compatibility := (rawFactor_laws J p χ f φ k τ).2

private theorem mapIsStronglyCartesian_laws {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] :
    (projection J p χ).IsHomLift f ((fromOriginal J p χ).map φ) ∧
    ∀ (c : Localized J p χ) (k : p.obj c.obj.obj ⟶ R)
      (τ : c ⟶ (fromOriginal J p χ).obj b) (hτ : (projection J p χ).IsHomLift (k ≫ f) τ),
      let value : c ⟶ (fromOriginal J p χ).obj a :=
        Quotient.mk'' (@rawFactor _ _ _ _ J p χ a b R S f φ hφ c k τ hτ)
      ((projection J p χ).IsHomLift k value ∧ value ≫ (fromOriginal J p χ).map φ = τ) ∧
      ∀ r : c ⟶ (fromOriginal J p χ).obj a,
        (projection J p χ).IsHomLift k r ∧ r ≫ (fromOriginal J p χ).map φ = τ → r = value := sorry

/-- Original strongly Cartesian arrows remain strongly Cartesian after localization. -/
theorem mapIsStronglyCartesian {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] :
    (projection J p χ).IsStronglyCartesian f ((fromOriginal J p χ).map φ) where
  toIsHomLift := (mapIsStronglyCartesian_laws J p χ f φ).1
  universal_property' := fun {c} k τ hτ ↦
    ⟨Quotient.mk'' (@rawFactor _ _ _ _ J p χ a b R S f φ hφ c k τ hτ),
      (mapIsStronglyCartesian_laws J p χ f φ).2 c k τ hτ⟩

/-- The local-arrow projection is fibered using the original cleavage lifts. -/
theorem isFibered : (projection J p χ).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  let l := χ.lift (x := a.obj.obj) f
  exact ⟨⟨⟨l.source⟩⟩, (fromOriginal J p χ).map l.hom,
    @mapIsStronglyCartesian _ _ _ _ J p χ l.source a.obj.obj R (p.obj a.obj.obj)
      f l.hom l.isStronglyCartesian⟩

private theorem comparison_laws : fromOriginal J p χ ⋙ projection J p χ = p := by
  refine Functor.ext (h_obj := fun _ ↦ rfl) ?_
  intro a b f
  change p.map f = 𝟙 (p.obj a) ≫ p.map f ≫ 𝟙 (p.obj b)
  simp

/-- The original category maps over the base to its local-morphism category. -/
def comparison : CartesianBasedFunctor p (projection J p χ) :=
  CartesianBasedFunctor.ofBasedFunctor
    { toFunctor := fromOriginal J p χ
      w := comparison_laws J p χ }
    (by
      intro a b φ hφ
      change (projection J p χ).IsStronglyCartesian
        ((projection J p χ).map ((fromOriginal J p χ).map φ)) ((fromOriginal J p χ).map φ)
      exact @mapIsStronglyCartesian _ _ _ _ J p χ a b (p.obj a) (p.obj b) (p.map φ) φ hφ)

/-- A compatible family of second-stage arrows on an actual cover. Each
component still has a native local-arrow representative, which can be flattened. -/
structure CoverFamily (a b : Localized J p χ) where
  /-- The common base arrow of the family. -/
  base : p.obj a.obj.obj ⟶ p.obj b.obj.obj
  /-- The covering sieve supporting the family. -/
  cover : J.Cover (p.obj a.obj.obj)
  /-- The localized arrow assigned to a covering arrow. -/
  arrow (I : cover.Arrow) :
    (fromOriginal J p χ).obj (sourceRestriction J p χ a.obj I.f) ⟶ b
  /-- Each component lies over the restriction of the common base arrow. -/
  isHomLift (I : cover.Arrow) :
    (projection J p χ).IsHomLift (I.f ≫ base) (arrow I)
  /-- Components agree under further Cartesian restriction. -/
  compatibility (I : cover.Arrow) {T : C} (k : T ⟶ I.Y) :
    (fromOriginal J p χ).map (refinementArrow J p χ a.obj I.f k) ≫ arrow I =
      arrow (I.precomp k)

namespace CoverFamily

/-- Native representatives of the supplied quotient classes. -/
def representative {a b : Localized J p χ} (d : CoverFamily J p χ a b)
    (I : d.cover.Arrow) :
    LocalArrow J p χ ((Separated.ofOriginal J p χ).obj
      (sourceRestriction J p χ a.obj I.f)) b.obj :=
  Quotient.out (d.arrow I)

/-- The common cover is the bind of the supplied cover and the actual covers
stored by the supplied quotient-arrow representatives. -/
def flattenCover {a b : Localized J p χ} (d : CoverFamily J p χ a b) :
    J.Cover (p.obj a.obj.obj) :=
  d.cover.bind fun I ↦
    (representative J p χ d I).cover.pullback
      (eqToHom (χ.reindexLift I.f (⟨a.obj.obj, rfl⟩ : p.Fiber (p.obj a.obj.obj))).sourceObj.symm)

private theorem flatten_numerator_isHomLift {a b : Localized J p χ}
    (d : CoverFamily J p χ a b) (K : (flattenCover J p χ d).Arrow) :
    p.IsHomLift K.toMiddle.base.f
      (refinementArrow J p χ a.obj K.fromMiddle.f K.toMiddleHom) := by
  exact (IsHomLift.lift_comp_eqToHom_iff p K.toMiddleHom
    (refinementArrow J p χ a.obj K.fromMiddle.f K.toMiddleHom)
    (χ.reindexLift K.fromMiddle.f
      (⟨a.obj.obj, rfl⟩ : p.Fiber (p.obj a.obj.obj))).sourceObj.symm).2
        (refinementArrow_isHomLift J p χ a.obj K.fromMiddle.f K.toMiddleHom)

private def flattenComponent {a b : Localized J p χ} (d : CoverFamily J p χ a b)
    (K : (flattenCover J p χ d).Arrow) :
    (Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a.obj K.f) ⟶ b.obj := by
  let I := K.fromMiddle
  let L := K.toMiddle
  let h := K.toMiddleHom
  let first := χ.reindexLift I.f (⟨a.obj.obj, rfl⟩ : p.Fiber (p.obj a.obj.obj))
  let second := χ.reindexLift L.base.f (⟨first.source, rfl⟩ : p.Fiber (p.obj first.source))
  let cartesian := @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
    C X _ _ p K.Y (p.obj first.source) second.source first.source L.base.f
    second.hom second.isStronglyCartesian
  let numerator := refinementArrow J p χ a.obj I.f h
  let numerator_lift : p.IsHomLift L.base.f numerator := flatten_numerator_isHomLift J p χ d K
  let factorArrow := @Functor.IsCartesian.map C X _ _ p K.Y (p.obj first.source)
    second.source first.source L.base.f second.hom cartesian
    (sourceRestriction J p χ a.obj (h ≫ I.f)) numerator numerator_lift
  exact eqToHom (congrArg ((Separated.ofOriginal J p χ).obj ∘ sourceRestriction J p χ a.obj)
    K.middle_spec.symm) ≫ (Separated.ofOriginal J p χ).map factorArrow ≫
      (representative J p χ d I).component L.base

private theorem flatten_laws {a b : Localized J p χ} (d : CoverFamily J p χ a b) :
    (∀ K : (flattenCover J p χ d).Arrow,
      (Separated.projection J p χ).IsHomLift (K.f ≫ d.base) (flattenComponent J p χ d K)) ∧
    (∀ (I : (flattenCover J p χ d).Arrow) {T : C} (k : T ⟶ I.Y),
      (Separated.ofOriginal J p χ).map (refinementArrow J p χ a.obj I.f k) ≫
        flattenComponent J p χ d I = flattenComponent J p χ d (I.precomp k)) := sorry

/-- Flatten the bound cover using the original Cartesian lift of each inner arrow. -/
def flatten {a b : Localized J p χ} (d : CoverFamily J p χ a b) :
    LocalArrow J p χ a.obj b.obj where
  base := d.base
  cover := flattenCover J p χ d
  component := flattenComponent J p χ d
  isHomLift := (flatten_laws J p χ d).1
  compatibility := (flatten_laws J p χ d).2

/-- The amalgamation is the quotient class of the flattened matching family. -/
def glue {a b : Localized J p χ} (d : CoverFamily J p χ a b) : a ⟶ b :=
  Quotient.mk'' (flatten J p χ d)

/-- Restriction of the explicit amalgamation recovers the supplied component. -/
theorem glue_restrict {a b : Localized J p χ} (d : CoverFamily J p χ a b)
    (I : d.cover.Arrow) :
    (fromOriginal J p χ).map (χ.cartesianHom I.f
      (⟨a.obj.obj, rfl⟩ : p.Fiber (p.obj a.obj.obj))) ≫ glue J p χ d = d.arrow I := sorry

/-- A compatible family determines its amalgamation uniquely over its base. -/
theorem glue_unique {a b : Localized J p χ} (d : CoverFamily J p χ a b)
    (τ : a ⟶ b) [(projection J p χ).IsHomLift d.base τ]
    (hτ : ∀ I : d.cover.Arrow,
      (fromOriginal J p χ).map (χ.cartesianHom I.f
        (⟨a.obj.obj, rfl⟩ : p.Fiber (p.obj a.obj.obj))) ≫ τ = d.arrow I) :
    τ = glue J p χ d := sorry

end CoverFamily

end Localized

end CategoryTheory.Functor.StackificationConstruction
