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
    map (f ≫ g) = map f ≫ map g := sorry

section FunctorImplementation

/-- Passing the identity morphism of an algebraic space to the homotopy category gives the
identity class. -/
theorem functor.map_id {S : Scheme.{u}} (F : AlgebraicSpace S) :
    Bicategory.HomotopyCategory.mkHom (map (𝟙 F)) =
      𝟙 (Bicategory.HomotopyCategory.mk F.toGroupoids) := sorry

/-- Passing composition of morphisms of algebraic spaces to the homotopy category gives
composition of their classes. -/
theorem functor.map_comp {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) :
    Bicategory.HomotopyCategory.mkHom (map (f ≫ g)) =
      Bicategory.HomotopyCategory.mkHom (map f) ≫
        Bicategory.HomotopyCategory.mkHom (map g) := sorry

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

/-- Recover a morphism of algebraic spaces from a `1`-morphism of the associated groupoid
fibrations by evaluating the induced fiber functors through the Grothendieck fiber-value
equivalence. -/
def eval {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) : F ⟶ G where
  app T := TypeCat.ofHom (eval.fiberMap φ (Opposite.unop T))
  naturality := sorry

/-- Evaluation of the canonical `1`-morphism associated to a morphism of algebraic spaces
recovers that morphism. -/
theorem eval.map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    eval (map f) = f := sorry

/-- A `2`-morphism of groupoid fibrations does not change the recovered morphism of algebraic
spaces. -/
theorem eval.eq_of_hom {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {φ ψ : F.toGroupoids ⟶ G.toGroupoids} (eta : φ ⟶ ψ) :
    eval φ = eval ψ := sorry

/-- `2`-isomorphic `1`-morphisms of groupoid fibrations recover the same morphism of algebraic
spaces. -/
theorem eval.eq_of_isomorphic {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {φ ψ : F.toGroupoids ⟶ G.toGroupoids} (h : IsIsomorphic φ ψ) :
    eval φ = eval ψ := sorry

/-- Evaluation of `1`-morphisms of associated groupoid fibrations is surjective on morphisms of
algebraic spaces. -/
theorem eval.surjective {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    Function.Surjective (eval : (F.toGroupoids ⟶ G.toGroupoids) → (F ⟶ G)) := sorry

/-- Two `1`-morphisms of associated groupoid fibrations recover the same morphism of algebraic
spaces exactly when they are `2`-isomorphic. -/
theorem eval.eq_iff_isomorphic {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ ψ : F.toGroupoids ⟶ G.toGroupoids) :
    eval φ = eval ψ ↔ IsIsomorphic φ ψ := sorry

/-- Evaluation as a functor to the discrete category of morphisms of algebraic spaces. -/
def eval.functor {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    (F.toGroupoids ⟶ G.toGroupoids) ⥤ Discrete (F ⟶ G) where
  obj φ := Discrete.mk (eval φ)
  map eta := Discrete.eqToHom (eval.eq_of_hom eta)

/-- Discrete evaluation sends a `1`-morphism to the recovered morphism of algebraic spaces. -/
@[simp]
theorem eval.functor.obj {S : Scheme.{u}} (F G : AlgebraicSpace S)
    (φ : F.toGroupoids ⟶ G.toGroupoids) :
    (eval.functor F G).obj φ = Discrete.mk (eval φ) := sorry

/-- The map of discrete evaluation is the equality morphism induced by invariance under the
given `2`-cell. -/
@[simp]
theorem eval.functor.map {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {φ ψ : F.toGroupoids ⟶ G.toGroupoids} (eta : φ ⟶ ψ) :
    (eval.functor F G).map eta = Discrete.eqToHom (eval.eq_of_hom eta) := sorry

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
    eval.desc F G (Bicategory.HomotopyCategory.mkHom φ) = eval φ := sorry

/-- Mapping a homotopy class after evaluation recovers the original class. -/
theorem eval.desc.map_preimage {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (f : Bicategory.HomotopyCategory.mk F.toGroupoids ⟶
      Bicategory.HomotopyCategory.mk G.toGroupoids) :
    (AlgebraicSpace.toGroupoids.functor S).map (eval.desc F G f) = f := sorry

/-- Evaluating the canonical image of a morphism of algebraic spaces recovers that morphism. -/
theorem eval.desc.preimage_map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    eval.desc F G ((AlgebraicSpace.toGroupoids.functor S).map f) = f := sorry

/-- The homotopy-category functor sends an algebraic space to the class of its groupoid
fibration. -/
@[simp]
theorem functor.obj {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (functor S).obj F = Bicategory.HomotopyCategory.mk F.toGroupoids := sorry

/-- The homotopy-category functor sends a morphism of algebraic spaces to the class of
`toGroupoids.map`. -/
@[simp]
theorem functor.map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (functor S).map f = Bicategory.HomotopyCategory.mkHom (map f) := sorry

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
    (functor.fullyFaithful S).preimage (Bicategory.HomotopyCategory.mkHom φ) = eval φ := sorry

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
    evalEquiv F G f = eval.desc F G f := sorry

/-- The forward map evaluates a represented homotopy class. -/
@[simp]
theorem evalEquiv.apply.mkHom {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (φ : F.toGroupoids ⟶ G.toGroupoids) :
    evalEquiv F G (Bicategory.HomotopyCategory.mkHom φ) = eval φ := sorry

/-- The inverse map is represented by the canonical `1`-morphism of groupoid fibrations. -/
@[simp]
theorem evalEquiv.symm.apply {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (evalEquiv F G).symm f = Bicategory.HomotopyCategory.mkHom (map f) := sorry

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
    recover eX eY φ = recover eX eY ψ := sorry

/-- Two morphisms of presented groupoid fibrations recover the same morphism of algebraic spaces
exactly when they are `2`-isomorphic. -/
theorem recover.eq_iff_isomorphic {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (φ ψ : X ⟶ Y) :
    recover eX eY φ = recover eX eY ψ ↔ IsIsomorphic φ ψ := sorry

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
    recover eX eY (ofHom eX eY f) = f := sorry

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
    homEquiv eX eY (Bicategory.HomotopyCategory.mkHom φ) = recover eX eY φ := sorry

/-- The inverse Hom equivalence is the homotopy class of the explicit presentation map. -/
@[simp]
theorem homEquiv.symm.apply {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) :
    (homEquiv eX eY).symm f =
      Bicategory.HomotopyCategory.mkHom (ofHom eX eY f) := sorry

/-- A `1`-morphism `φ : X ⟶ Y` induces `f : F ⟶ G` relative to presentations `eX` and `eY`
when `φ ≫ eY.hom` is `2`-isomorphic to `eX.hom ≫ toGroupoids.map f`. -/
def InducesHom {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (φ : X ⟶ Y) (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (f : F ⟶ G) : Prop :=
  Nonempty ((φ ≫ eY.hom) ≅ (eX.hom ≫ map f))

/-- The explicit presentation map induces the morphism of algebraic spaces from which it was
constructed. -/
theorem ofHom.induces {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (f : F ⟶ G) :
    InducesHom (ofHom eX eY f) eX eY f := sorry

/-- The morphism of algebraic spaces recovered from a `1`-morphism is induced by that
`1`-morphism. -/
theorem InducesHom.recover {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids) (φ : X ⟶ Y) :
    InducesHom φ eX eY (toGroupoids.recover eX eY φ) := sorry

/-- A `1`-morphism induces `f` exactly when its recovered morphism of algebraic spaces is `f`. -/
theorem InducesHom.iff_recover_eq {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (φ : X ⟶ Y) (f : F ⟶ G) :
    InducesHom φ eX eY f ↔ toGroupoids.recover eX eY φ = f := sorry

/-- Every morphism of algebraic spaces is induced by a `1`-morphism of the presented groupoid
fibrations. -/
theorem InducesHom.exists_morphism {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) :
    ∃ φ : X ⟶ Y, InducesHom φ eX eY f := sorry

/-- Two `1`-morphisms inducing the same morphism of algebraic spaces are `2`-isomorphic. -/
theorem InducesHom.nonempty_iso {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) {φ ψ : X ⟶ Y}
    (hφ : InducesHom φ eX eY f) (hψ : InducesHom ψ eX eY f) :
    Nonempty (φ ≅ ψ) := sorry

/-- The `2`-isomorphism between two `1`-morphisms inducing the same morphism of algebraic spaces
is unique. -/
theorem InducesHom.iso_ext {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : F ⟶ G) {φ ψ : X ⟶ Y}
    (hφ : InducesHom φ eX eY f) (hψ : InducesHom ψ eX eY f)
    (α β : φ ≅ ψ) : α = β := sorry

end AlgebraicGeometry.AlgebraicSpace.toGroupoids
