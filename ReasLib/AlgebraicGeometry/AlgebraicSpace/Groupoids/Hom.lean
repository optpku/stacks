/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.HomCongr
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.LocallyGroupoidal
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids

/-!
# Homotopy-category functor of algebraic spaces

The discrete Grothendieck construction `S_F` of an algebraic space over `S` is functorial in
morphisms of algebraic spaces. Passing to the homotopy `1`-category of `GroupoidsOver S`
identifies `1`-morphisms of the associated groupoid fibrations up to `2`-isomorphism with
morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Opposite TypeCat
open FiberedCategoryOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.toGroupoids

/-- `toGroupoids.map` preserves composition of morphisms of algebraic spaces. -/
theorem map_comp {S : Scheme.{u}} {F G H : AlgebraicSpace S} (f : F ⟶ G) (g : G ⟶ H) :
    map (f ≫ g) = map f ≫ map g := by
  rfl

section FunctorImplementation

/-- Passing the identity morphism of an algebraic space to the homotopy category gives the
identity class. -/
theorem functor.map_id {S : Scheme.{u}} (F : AlgebraicSpace S) :
    Bicategory.HomotopyCategory.mkHom (map (𝟙 F)) =
      𝟙 (Bicategory.HomotopyCategory.mk F.toGroupoids) := by
  rfl

/-- Passing composition of morphisms of algebraic spaces to the homotopy category gives
composition of their classes. -/
theorem functor.map_comp {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) :
    Bicategory.HomotopyCategory.mkHom (map (f ≫ g)) =
      Bicategory.HomotopyCategory.mkHom (map f) ≫
        Bicategory.HomotopyCategory.mkHom (map g) := by
  rw [toGroupoids.map_comp]
  rfl

/-- The functor sending an algebraic space over `S` to its groupoid fibration in the homotopy
category of `GroupoidsOver S`. -/
def functor (S : Scheme.{u}) :
    AlgebraicSpace S ⥤ Bicategory.HomotopyCategory (GroupoidsOver S) where
  obj F := Bicategory.HomotopyCategory.mk F.toGroupoids
  map f := Bicategory.HomotopyCategory.mkHom (map f)
  map_id F := functor.map_id F
  map_comp f g := functor.map_comp f g

end FunctorImplementation

/-- Fiberwise evaluation of a `1`-morphism at a scheme over `S`. -/
def eval.fiberMap {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) (U : Over S) :
    F.functorOfPoints.obj (Opposite.op U) → G.functorOfPoints.obj (Opposite.op U) :=
  fun x ↦
    Sets.ofPresheaf.fiberToValue G.functorOfPoints U
      ((fiberFunctor φ U).obj (Sets.ofPresheaf.valueToFiber F.functorOfPoints U x))

/-- A morphism in the category of elements computes restriction after the fiber transports. -/
private theorem fiberToValue_map {S : Scheme.{u}} (G : AlgebraicSpace S)
    {U V : Over S} (f : U ⟶ V)
    (a : G.toGroupoids.p.Fiber U) (b : G.toGroupoids.p.Fiber V)
    (k : a.1 ⟶ b.1) (hk : G.toGroupoids.p.IsHomLift f k) :
    G.functorOfPoints.map f.op (Sets.ofPresheaf.fiberToValue G.functorOfPoints V b) =
      Sets.ofPresheaf.fiberToValue G.functorOfPoints U a := by
  letI := hk
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  subst U V
  have hk := IsHomLift.eq_of_isHomLift G.toGroupoids.p f k
  subst f
  change G.functorOfPoints.map k.unop.val
      (G.functorOfPoints.map (𝟙 _) b.unop.2) =
    G.functorOfPoints.map (𝟙 _) a.unop.2
  simpa using k.unop.property

/-- Fiberwise evaluation is natural in the test scheme. Keeping this law named prevents
unfolding `eval` from inserting an inline proof placeholder into downstream types. -/
theorem eval.naturality {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    F.functorOfPoints.map f ≫ TypeCat.ofHom (eval.fiberMap φ (Opposite.unop V)) =
      TypeCat.ofHom (eval.fiberMap φ (Opposite.unop U)) ≫ G.functorOfPoints.map f := by
  apply ConcreteCategory.hom_ext
  intro x
  let a := Sets.ofPresheaf.valueToFiber F.functorOfPoints U.unop x
  let b := Sets.ofPresheaf.valueToFiber F.functorOfPoints V.unop
    (F.functorOfPoints.map f x)
  let k : b.1 ⟶ a.1 := (CategoryOfElements.homMk a.1.unop b.1.unop f rfl).op
  letI : F.toGroupoids.p.IsHomLift f.unop k := Functor.IsHomLift.map k
  exact (fiberToValue_map G f.unop
    ((fiberFunctor φ V.unop).obj b) ((fiberFunctor φ U.unop).obj a)
    (φ.hom.map k) (BasedFunctor.preserves_isHomLift φ.hom f.unop k)).symm

/-- Recover a morphism of algebraic spaces from a `1`-morphism of the associated groupoid
fibrations by evaluating the induced fiber functors through the Grothendieck fiber-value
equivalence. -/
def eval {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) : F ⟶ G where
  app T := TypeCat.ofHom (eval.fiberMap φ (Opposite.unop T))
  naturality := fun {_ _} f ↦ eval.naturality φ f

/-- Evaluation of the canonical `1`-morphism associated to a morphism of algebraic spaces
recovers that morphism. -/
theorem eval.map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    eval (map f) = f := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  change G.functorOfPoints.map (𝟙 U) (f.app U x) = f.app U x
  simp

/-- A `2`-morphism of groupoid fibrations does not change the recovered morphism of algebraic
spaces. -/
theorem eval.eq_of_hom {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {φ ψ : F.toGroupoids ⟶ G.toGroupoids} (eta : φ ⟶ ψ) :
    eval φ = eval ψ := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  let a := Sets.ofPresheaf.valueToFiber F.functorOfPoints U.unop x
  let k := BasedNatTrans.fiberApp eta.hom U.unop a
  change Sets.ofPresheaf.fiberToValue G.functorOfPoints U.unop
      ((fiberFunctor φ U.unop).obj a) =
    Sets.ofPresheaf.fiberToValue G.functorOfPoints U.unop
      ((fiberFunctor ψ U.unop).obj a)
  simpa using (fiberToValue_map G (𝟙 U.unop)
    ((fiberFunctor φ U.unop).obj a) ((fiberFunctor ψ U.unop).obj a) k.1 k.2).symm

/-- `2`-isomorphic `1`-morphisms of groupoid fibrations recover the same morphism of algebraic
spaces. -/
theorem eval.eq_of_isomorphic {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {φ ψ : F.toGroupoids ⟶ G.toGroupoids} (h : IsIsomorphic φ ψ) :
    eval φ = eval ψ := by
  rcases h with ⟨e⟩
  exact eval.eq_of_hom e.hom

/-- Evaluation of `1`-morphisms of associated groupoid fibrations is surjective on morphisms of
algebraic spaces. -/
theorem eval.surjective {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    Function.Surjective (eval : (F.toGroupoids ⟶ G.toGroupoids) → (F ⟶ G)) := by
  intro f
  exact ⟨toGroupoids.map f, eval.map f⟩

/-- The category-of-elements projection is faithful after forgetting to groupoids. -/
private theorem projection_faithful {S : Scheme.{u}} (G : AlgebraicSpace S) :
    G.toGroupoids.p.Faithful := by
  change ((CategoryOfElements.π G.functorOfPoints).leftOp).Faithful
  infer_instance

/-- Evaluation records the image of every object of the category of elements. -/
private theorem eval_obj_eq {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) (a : F.toGroupoids.total) :
    (toFunctor φ).obj a = (toFunctor (toGroupoids.map (eval φ))).obj a := by
  exact (congrArg Subtype.val
    (Sets.ofPresheaf.valueToFiber.leftInverse G.functorOfPoints
      (F.toGroupoids.p.obj a)
      ((fiberFunctor φ (F.toGroupoids.p.obj a)).obj
        (Sets.ofPresheaf.valueToFiber F.functorOfPoints
          (F.toGroupoids.p.obj a) a.unop.2)))).symm

/-- Two `1`-morphisms of associated groupoid fibrations recover the same morphism of algebraic
spaces exactly when they are `2`-isomorphic. -/
theorem eval.eq_iff_isomorphic {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ ψ : F.toGroupoids ⟶ G.toGroupoids) :
    eval φ = eval ψ ↔ IsIsomorphic φ ψ := by
  constructor
  · intro h
    have hobj (a : F.toGroupoids.total) : φ.hom.obj a = ψ.hom.obj a :=
      (eval_obj_eq φ a).trans
        ((congrArg (fun f : F ⟶ G ↦ (toFunctor (toGroupoids.map f)).obj a) h).trans
          (eval_obj_eq ψ a).symm)
    have hv (a : F.toGroupoids.total) :
        G.toGroupoids.p.IsHomLift (𝟙 (F.toGroupoids.p.obj a)) (eqToHom (hobj a)) :=
      IsHomLift.eqToHom_domain_lift_id (hobj a) (φ.hom.w_obj a)
    refine ⟨Bicategory.InducedBicategory.isoMk
      (BasedNatIso.ofComponents (fun a ↦ eqToIso (hobj a)) ?_ hv)⟩
    intro a b k
    change φ.hom.map k ≫ eqToHom (hobj b) = eqToHom (hobj a) ≫ ψ.hom.map k
    letI := hv a
    letI := hv b
    letI : G.toGroupoids.p.IsHomLift (F.toGroupoids.p.map k) (φ.hom.map k) :=
      BasedFunctor.preserves_isHomLift φ.hom _ k
    letI : G.toGroupoids.p.IsHomLift (F.toGroupoids.p.map k) (ψ.hom.map k) :=
      BasedFunctor.preserves_isHomLift ψ.hom _ k
    letI : G.toGroupoids.p.IsHomLift (F.toGroupoids.p.map k)
        (φ.hom.map k ≫ eqToHom (hobj b)) :=
      IsHomLift.comp_lift_id_right G.toGroupoids.p _ _ _
    letI : G.toGroupoids.p.IsHomLift (F.toGroupoids.p.map k)
        (eqToHom (hobj a) ≫ ψ.hom.map k) :=
      IsHomLift.comp_lift_id_left G.toGroupoids.p _ _ _
    letI := projection_faithful G
    apply G.toGroupoids.p.map_injective
    exact (IsHomLift.fac' G.toGroupoids.p (F.toGroupoids.p.map k) _).trans
      (IsHomLift.fac' G.toGroupoids.p (F.toGroupoids.p.map k) _).symm
  · exact eval.eq_of_isomorphic

/-- Evaluation as a functor to the discrete category of morphisms of algebraic spaces. -/
def eval.functor {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    (F.toGroupoids ⟶ G.toGroupoids) ⥤ Discrete (F ⟶ G) where
  obj φ := Discrete.mk (eval φ)
  map eta := Discrete.eqToHom (eval.eq_of_hom eta)

/-- Discrete evaluation sends a `1`-morphism to the recovered morphism of algebraic spaces. -/
@[simp]
theorem eval.functor.obj {S : Scheme.{u}} (F G : AlgebraicSpace S)
    (φ : F.toGroupoids ⟶ G.toGroupoids) :
    (eval.functor F G).obj φ = Discrete.mk (eval φ) := rfl

/-- The map of discrete evaluation is the equality morphism induced by invariance under the
given `2`-cell. -/
@[simp]
theorem eval.functor.map {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {φ ψ : F.toGroupoids ⟶ G.toGroupoids} (eta : φ ⟶ ψ) :
    (eval.functor F G).map eta = Discrete.eqToHom (eval.eq_of_hom eta) := rfl

/-- Evaluation descended to homotopy classes of `1`-morphisms of associated groupoid
fibrations. -/
def eval.desc {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    (Bicategory.HomotopyCategory.mk F.toGroupoids ⟶
      Bicategory.HomotopyCategory.mk G.toGroupoids) → (F ⟶ G) :=
  ConnectedComponents.liftFunctor _ (eval.functor F G)

/-- Descended evaluation computes on a represented class by evaluating its representative. -/
@[simp]
theorem eval.desc.mkHom {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) :
    eval.desc F G (Bicategory.HomotopyCategory.mkHom φ) = eval φ := rfl

/-- Mapping a homotopy class after evaluation recovers the original class. -/
theorem eval.desc.map_preimage {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (f : Bicategory.HomotopyCategory.mk F.toGroupoids ⟶
      Bicategory.HomotopyCategory.mk G.toGroupoids) :
    (AlgebraicSpace.toGroupoids.functor S).map (eval.desc F G f) = f := by
  refine Quotient.inductionOn f ?_
  intro φ
  change Bicategory.HomotopyCategory.mkHom (toGroupoids.map (eval φ)) =
    Bicategory.HomotopyCategory.mkHom φ
  exact Bicategory.HomotopyCategory.mkHom.eq_iff_isomorphic.mpr
    ((eval.eq_iff_isomorphic _ _).mp (eval.map (eval φ)))

/-- Evaluating the canonical image of a morphism of algebraic spaces recovers that morphism. -/
theorem eval.desc.preimage_map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    eval.desc F G ((AlgebraicSpace.toGroupoids.functor S).map f) = f := by
  exact eval.map f

/-- The homotopy-category functor sends an algebraic space to the class of its groupoid
fibration. -/
@[simp]
theorem functor.obj {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (functor S).obj F = Bicategory.HomotopyCategory.mk F.toGroupoids := rfl

/-- The homotopy-category functor sends a morphism of algebraic spaces to the class of
`toGroupoids.map`. -/
@[simp]
theorem functor.map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (functor S).map f = Bicategory.HomotopyCategory.mkHom (map f) := rfl

/-- The homotopy-category functor of algebraic spaces is fully faithful; its preimage is
descended fiberwise evaluation. -/
def functor.fullyFaithful (S : Scheme.{u}) : (functor S).FullyFaithful where
  preimage {F G} := eval.desc F G
  map_preimage := eval.desc.map_preimage
  preimage_map := eval.desc.preimage_map

/-- The homotopy-category functor of algebraic spaces is full. -/
instance functor.full (S : Scheme.{u}) : (functor S).Full :=
  (functor.fullyFaithful S).full

/-- The homotopy-category functor of algebraic spaces is faithful. -/
instance functor.faithful (S : Scheme.{u}) : (functor S).Faithful :=
  (functor.fullyFaithful S).faithful

/-- The preimage supplied by full faithfulness evaluates represented homotopy classes. -/
@[simp]
theorem functor.fullyFaithful.preimage_mkHom {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) :
    (functor.fullyFaithful S).preimage (Bicategory.HomotopyCategory.mkHom φ) = eval φ := rfl

/-- Homotopy classes of `1`-morphisms between the groupoid fibrations of algebraic spaces are
canonically equivalent to morphisms of those algebraic spaces. -/
def evalEquiv {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    (Bicategory.HomotopyCategory.mk F.toGroupoids ⟶
      Bicategory.HomotopyCategory.mk G.toGroupoids) ≃ (F ⟶ G) :=
  (functor.fullyFaithful S).homEquiv.symm

/-- The forward map of the identity-presentation Hom equivalence is descended fiberwise
evaluation. -/
@[simp]
theorem evalEquiv.apply {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (f : Bicategory.HomotopyCategory.mk F.toGroupoids ⟶
      Bicategory.HomotopyCategory.mk G.toGroupoids) :
    evalEquiv F G f = eval.desc F G f := rfl

/-- The forward map evaluates a represented homotopy class. -/
@[simp]
theorem evalEquiv.apply.mkHom {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) :
    evalEquiv F G (Bicategory.HomotopyCategory.mkHom φ) = eval φ := rfl

/-- The inverse map is represented by the canonical `1`-morphism of groupoid fibrations. -/
@[simp]
theorem evalEquiv.symm.apply {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (evalEquiv F G).symm f = Bicategory.HomotopyCategory.mkHom (map f) := rfl

/-- Recover a morphism of algebraic spaces from a `1`-morphism of presented groupoid fibrations
by transporting to the associated `S_F` and `S_G` and evaluating. -/
def recover {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (φ : X ⟶ Y) : F ⟶ G :=
  eval ((eX.inv ≫ φ) ≫ eY.hom)

/-- `2`-isomorphic morphisms through the same presentations recover the same morphism of
algebraic spaces. -/
theorem recover.eq_of_isomorphic {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    {φ ψ : X ⟶ Y} (h : IsIsomorphic φ ψ) :
    recover eX eY φ = recover eX eY ψ := by
  rcases h with ⟨e⟩
  exact eval.eq_of_isomorphic
    ⟨Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso eX.inv e) eY.hom⟩

/-- Two morphisms of presented groupoid fibrations recover the same morphism of algebraic spaces
exactly when they are `2`-isomorphic. -/
theorem recover.eq_iff_isomorphic {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (φ ψ : X ⟶ Y) :
    recover eX eY φ = recover eX eY ψ ↔ IsIsomorphic φ ψ := by
  change eval ((eX.inv ≫ φ) ≫ eY.hom) =
      eval ((eX.inv ≫ ψ) ≫ eY.hom) ↔ _
  rw [eval.eq_iff_isomorphic,
    ← Bicategory.HomotopyCategory.mkHom.eq_iff_isomorphic,
    ← Bicategory.HomotopyCategory.mkHom.eq_iff_isomorphic]
  change (Iso.homCongr (Bicategory.HomotopyCategory.isoOfEquivalence eX)
      (Bicategory.HomotopyCategory.isoOfEquivalence eY))
        (Bicategory.HomotopyCategory.mkHom φ) =
    (Iso.homCongr (Bicategory.HomotopyCategory.isoOfEquivalence eX)
      (Bicategory.HomotopyCategory.isoOfEquivalence eY))
        (Bicategory.HomotopyCategory.mkHom ψ) ↔ _
  exact Equiv.injective _ |>.eq_iff

/-- Transport a morphism of algebraic spaces back through chosen presentations as a `1`-morphism
of groupoid fibrations. -/
def ofHom {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (f : F ⟶ G) : X ⟶ Y :=
  (eX.hom ≫ map f) ≫ eY.inv

/-- Recovering the explicit presentation map returns the original morphism of algebraic
spaces. -/
@[simp]
theorem recover.ofHom {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (f : F ⟶ G) :
    recover eX eY (ofHom eX eY f) = f := by
  let iX := Bicategory.HomotopyCategory.isoOfEquivalence eX
  let iY := Bicategory.HomotopyCategory.isoOfEquivalence eY
  have h : Bicategory.HomotopyCategory.mkHom
      ((eX.inv ≫ toGroupoids.ofHom eX eY f) ≫ eY.hom) =
        Bicategory.HomotopyCategory.mkHom (map f) := by
    change (iX.inv ≫ ((iX.hom ≫ Bicategory.HomotopyCategory.mkHom (map f)) ≫
      iY.inv)) ≫ iY.hom = _
    simp [Category.assoc]
  exact (congrArg (eval.desc F G) h).trans (eval.map f)

/-- Homotopy classes of `1`-morphisms of groupoid fibrations presented by algebraic spaces `F`
and `G` are canonically equivalent to morphisms `F ⟶ G`. -/
def homEquiv {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) :
    (Bicategory.HomotopyCategory.mk X ⟶ Bicategory.HomotopyCategory.mk Y) ≃ (F ⟶ G) :=
  (Iso.homCongr
      (Bicategory.HomotopyCategory.isoOfEquivalence eX)
      (Bicategory.HomotopyCategory.isoOfEquivalence eY)).trans
    (evalEquiv F G)

/-- The represented Hom equivalence evaluates a transported representative. -/
@[simp]
theorem homEquiv.apply.mkHom {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (φ : X ⟶ Y) :
    homEquiv eX eY (Bicategory.HomotopyCategory.mkHom φ) = recover eX eY φ := rfl

/-- The inverse Hom equivalence is the homotopy class of the explicit presentation map. -/
@[simp]
theorem homEquiv.symm.apply {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) :
    (homEquiv eX eY).symm f =
      Bicategory.HomotopyCategory.mkHom (ofHom eX eY f) := rfl

/-- A `1`-morphism `φ : X ⟶ Y` induces `f : F ⟶ G` relative to presentations `eX` and `eY`
when `φ ≫ eY.hom` is `2`-isomorphic to `eX.hom ≫ toGroupoids.map f`. -/
def InducesHom {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (φ : X ⟶ Y) (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (f : F ⟶ G) : Prop :=
  Nonempty ((φ ≫ eY.hom) ≅ (eX.hom ≫ map f))

/-- The explicit presentation map induces the morphism of algebraic spaces from which it was
constructed. -/
theorem ofHom.induces {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (f : F ⟶ G) :
    InducesHom (ofHom eX eY f) eX eY f := by
  refine ⟨Bicategory.associator (eX.hom ≫ map f) eY.inv eY.hom ≪≫
    Bicategory.whiskerLeftIso (eX.hom ≫ map f) eY.counit ≪≫
    Bicategory.rightUnitor (eX.hom ≫ map f)⟩

/-- The morphism of algebraic spaces recovered from a `1`-morphism is induced by that
`1`-morphism. -/
theorem InducesHom.recover {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (φ : X ⟶ Y) :
    InducesHom φ eX eY (toGroupoids.recover eX eY φ) := by
  have h : toGroupoids.recover eX eY φ =
      toGroupoids.recover eX eY (ofHom eX eY (toGroupoids.recover eX eY φ)) :=
    (recover.ofHom eX eY _).symm
  rcases (recover.eq_iff_isomorphic eX eY _ _).mp h with ⟨e⟩
  rcases ofHom.induces eX eY (toGroupoids.recover eX eY φ) with ⟨i⟩
  exact ⟨Bicategory.whiskerRightIso e eY.hom ≪≫ i⟩

/-- A `1`-morphism induces `f` exactly when its recovered morphism of algebraic spaces is `f`. -/
theorem InducesHom.iff_recover_eq {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (φ : X ⟶ Y) (f : F ⟶ G) :
    InducesHom φ eX eY f ↔ toGroupoids.recover eX eY φ = f := by
  change IsIsomorphic (φ ≫ eY.hom) (eX.hom ≫ map f) ↔ _
  rw [← Bicategory.HomotopyCategory.mkHom.eq_iff_isomorphic]
  let iX := Bicategory.HomotopyCategory.isoOfEquivalence eX
  let iY := Bicategory.HomotopyCategory.isoOfEquivalence eY
  change Bicategory.HomotopyCategory.mkHom φ ≫ iY.hom =
      iX.hom ≫ Bicategory.HomotopyCategory.mkHom (map f) ↔ _
  rw [← iX.inv_comp_eq]
  rw [← (evalEquiv F G).injective.eq_iff]
  change eval ((eX.inv ≫ φ) ≫ eY.hom) = eval (map f) ↔ _
  rw [eval.map]
  rfl

/-- Every morphism of algebraic spaces is induced by a `1`-morphism of the presented groupoid
fibrations. -/
theorem InducesHom.exists_morphism {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) :
    ∃ φ : X ⟶ Y, InducesHom φ eX eY f := by
  exact ⟨ofHom eX eY f, ofHom.induces eX eY f⟩

/-- Two `1`-morphisms inducing the same morphism of algebraic spaces are `2`-isomorphic. -/
theorem InducesHom.nonempty_iso {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) {φ ψ : X ⟶ Y}
    (hφ : InducesHom φ eX eY f) (hψ : InducesHom ψ eX eY f) :
    Nonempty (φ ≅ ψ) := by
  apply (recover.eq_iff_isomorphic eX eY φ ψ).mp
  exact ((InducesHom.iff_recover_eq eX eY φ f).mp hφ).trans
    ((InducesHom.iff_recover_eq eX eY ψ f).mp hψ).symm

/-- Vertical transformations into the discrete Grothendieck construction are unique. -/
private theorem twoCell_ext {S : Scheme.{u}} {G : AlgebraicSpace S}
    {X : GroupoidsOver S} {φ ψ : X ⟶ G.toGroupoids} (α β : φ ⟶ ψ) : α = β := by
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  letI := projection_faithful G
  apply G.toGroupoids.p.map_injective
  exact (IsHomLift.fac' G.toGroupoids.p (𝟙 (X.p.obj a)) _).trans
    (IsHomLift.fac' G.toGroupoids.p (𝟙 (X.p.obj a)) _).symm

/-- The `2`-isomorphism between two `1`-morphisms inducing the same morphism of algebraic spaces
is unique. -/
theorem InducesHom.iso_ext {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) {φ ψ : X ⟶ Y}
    (hφ : InducesHom φ eX eY f) (hψ : InducesHom ψ eX eY f)
    (α β : φ ≅ ψ) : α = β := by
  clear hφ hψ
  apply Iso.ext
  apply (Bicategory.postcomp X eY.hom).map_injective
  exact twoCell_ext _ _

end AlgebraicGeometry.AlgebraicSpace.toGroupoids
