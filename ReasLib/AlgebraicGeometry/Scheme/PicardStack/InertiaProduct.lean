/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Representable.Stack
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.AlgebraicGeometry.Scheme.PicardStack

/-!
# Multiplicative group times the Picard stack

The representable stack of `𝔾ₘ[S]` and the explicit product stack
`𝔾ₘ[S] ×_S Pic_{X/S}`, together with the comparison from inertia.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Picard

/-- The representable presheaf of `𝔾ₘ[S]` is a sheaf on `(Sch/S)_fppf`. -/
theorem mulGroupStack_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj (𝔾ₘ[S]).X) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The stack in groupoids represented by `𝔾ₘ[S]` over `(Sch/S)_fppf`. -/
def mulGroupStack (S : Scheme.{u}) :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  (Over.representableStack (Scheme.fppfTopology.over S) (𝔾ₘ[S]).X
    (mulGroupStack_isSheaf S)).toGroupoids

/-- An object of `𝔾ₘ[S] ×_S Pic_{X/S}` is a Picard object together with a `T`-point of `𝔾ₘ[S]`. -/
structure ProductObj {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The underlying Picard object. -/
  pic : Obj f
  /-- The `𝔾ₘ[S]`-point of the test object. -/
  mul : pic.base ⟶ (𝔾ₘ[S]).X

/-- Package a Picard object and a `𝔾ₘ[S]`-point as a product object. -/
def ProductObj.ofPair {X S : Scheme.{u}} {f : X ⟶ S} (pic : Obj f)
    (mul : pic.base ⟶ (𝔾ₘ[S]).X) : ProductObj f where
  pic := pic
  mul := mul

/-- A morphism of product objects is a Picard morphism commuting with the `𝔾ₘ[S]`-points. -/
structure ProductHom {X S : Scheme.{u}} {f : X ⟶ S} (x y : ProductObj f) where
  /-- The underlying Picard morphism. -/
  pic : Hom x.pic y.pic
  /-- The `𝔾ₘ[S]`-points are compatible with the test map. -/
  mul_w : pic.base ≫ y.mul = x.mul

/-- Product morphisms are determined by their underlying Picard morphisms. -/
@[ext] theorem ProductHom.ext {X S : Scheme.{u}} {f : X ⟶ S} {x y : ProductObj f}
    {α β : ProductHom x y} (h : α.pic = β.pic) : α = β := by
  cases α
  cases β
  cases h
  rfl

/-- The identity morphism of a product object. -/
def ProductHom.id {X S : Scheme.{u}} {f : X ⟶ S} (x : ProductObj f) :
    ProductHom x x where
  pic := Hom.id x.pic
  mul_w := Category.id_comp _

/-- Composition of product morphisms. -/
def ProductHom.comp {X S : Scheme.{u}} {f : X ⟶ S} {x y z : ProductObj f}
    (α : ProductHom x y) (β : ProductHom y z) : ProductHom x z where
  pic := Hom.compHom α.pic β.pic
  mul_w :=
    Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun k => α.pic.base ≫ k) β.mul_w) α.mul_w)

/-- Composing a product morphism with the identity on its source leaves it unchanged. -/
theorem ProductHom.id_comp {X S : Scheme.{u}} {f : X ⟶ S} {x y : ProductObj f}
    (α : ProductHom x y) : ProductHom.comp (ProductHom.id x) α = α := by
  apply ProductHom.ext
  exact @Category.id_comp (Obj f) (category f) x.pic y.pic α.pic

/-- Composing a product morphism with the identity on its target leaves it unchanged. -/
theorem ProductHom.comp_id {X S : Scheme.{u}} {f : X ⟶ S} {x y : ProductObj f}
    (α : ProductHom x y) : ProductHom.comp α (ProductHom.id y) = α := by
  apply ProductHom.ext
  exact @Category.comp_id (Obj f) (category f) x.pic y.pic α.pic

/-- Composition of product morphisms is associative. -/
theorem ProductHom.assoc {X S : Scheme.{u}} {f : X ⟶ S} {w x y z : ProductObj f}
    (α : ProductHom w x) (β : ProductHom x y) (γ : ProductHom y z) :
    ProductHom.comp (ProductHom.comp α β) γ = ProductHom.comp α (ProductHom.comp β γ) := by
  apply ProductHom.ext
  exact @Category.assoc (Obj f) (category f) w.pic x.pic y.pic z.pic α.pic β.pic γ.pic

/-- Product objects form a category. -/
@[reducible] def productCategory {X S : Scheme.{u}} (f : X ⟶ S) :
    Category (ProductObj f) where
  Hom := ProductHom
  id := ProductHom.id
  comp := ProductHom.comp
  id_comp := ProductHom.id_comp
  comp_id := ProductHom.comp_id
  assoc := ProductHom.assoc

/-- The projection of the product category to `(Sch/S)_fppf`. -/
def ProductObj.p {X S : Scheme.{u}} (f : X ⟶ S) :
    @Functor (ProductObj f) (productCategory f) (Over S) inferInstance :=
  @CategoryTheory.Functor.mk (ProductObj f) (productCategory f) (Over S) inferInstance
    (fun x => x.pic.base) (fun {_ _} α => α.pic.base)
    (fun _ => Eq.refl _) (fun {_ _ _} _ _ => Eq.refl _)

/-- The first projection of a product object is its `𝔾ₘ[S]`-point. -/
def ProductObj.fst {X S : Scheme.{u}} {f : X ⟶ S} (x : ProductObj f) :
    x.pic.base ⟶ (𝔾ₘ[S]).X :=
  x.mul

/-- The second projection of a product object is its Picard object. -/
def ProductObj.snd {X S : Scheme.{u}} {f : X ⟶ S} (x : ProductObj f) : Obj f :=
  x.pic

/-- The product projection is a stack in groupoids on `(Sch/S)_fppf`. -/
theorem ProductObj.p_isStack {X S : Scheme.{u}} (f : X ⟶ S) :
    @IsStack.InGroupoids (Over S) (ProductObj f) inferInstance (productCategory f)
      (Scheme.fppfTopology.over S) (ProductObj.p f) :=
  sorry

/-- The product stack `𝔾ₘ[S] ×_S Pic_{X/S}` over `(Sch/S)_fppf`. -/
def mulGroupProduct {X S : Scheme.{u}} (f : X ⟶ S) :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  @StackOver.Groupoids.ofProjectionWith (Over S) inferInstance
    (Scheme.fppfTopology.over S) (ProductObj f) (productCategory f)
    (ProductObj.p f) (ProductObj.p_isStack f)

/-- The projection of `mulGroupProduct f` is the product projection. -/
theorem mulGroupProduct_p {X S : Scheme.{u}} (f : X ⟶ S) :
    (mulGroupProduct f).p = ProductObj.p f :=
  rfl

/-- Transport global units of `X_T` to global units of `T` by the structure-sheaf isomorphism. -/
def unitsRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] (T : Over S)
    (u : Γ(pullback f T.hom, ⊤)ˣ) : Γ(T.left, ⊤)ˣ :=
  let φ := (pullback.snd f T.hom).commRingSheafPushforwardMap
  Units.map ((CategoryTheory.inv φ).hom.app
    (Opposite.op (⊤ : T.left.Opens))).hom.toMonoidHom u

set_option backward.privateInPublic true in
/-- The base morphism of a vertical inertia automorphism is the identity. -/
private theorem inertia_aut_base_eq_id {X S : Scheme.{u}} {f : X ⟶ S}
    (ξ : @RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f)) :
    (@Iso.hom _ (category f) _ _
      (@Inertia.aut _ (category f)
        (@RelativeInertia.toInertia _ (category f) _ _ _ ξ))).base =
      𝟙 (@Inertia.obj _ (category f)
        (@RelativeInertia.toInertia _ (category f) _ _ _ ξ)).base :=
  congrArg Iso.hom (@RelativeInertia.mapAut_eq_one _ (category f) _ _ _ ξ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- An inertia object of the Picard stack determines an automorphism of its line bundle. -/
def inertiaAutLine {X S : Scheme.{u}} {f : X ⟶ S}
    (ξ : @RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f)) :
    Aut (@Inertia.obj _ (category f)
      (@RelativeInertia.toInertia _ (category f) _ _ _ ξ)).line :=
  autOfVertical
    (@Iso.hom _ (category f) _ _
      (@Inertia.aut _ (category f)
        (@RelativeInertia.toInertia _ (category f) _ _ _ ξ)))
    (inertia_aut_base_eq_id ξ)

/-- The object map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulObj {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f]
    (ξ : @RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f)) :
    ProductObj f :=
  let obj := @Inertia.obj _ (category f)
    (@RelativeInertia.toInertia _ (category f) _ _ _ ξ)
  { pic := obj
    mul := (MultiplicativeGroup.baseChangeHomEquiv S obj.base).symm
      (unitsRestrict f obj.base (autToUnits obj.line obj.invertible (inertiaAutLine ξ))) }

set_option backward.privateInPublic true in
/-- The multiplicative-group points associated to inertia objects commute with inertia arrows. -/
private theorem inertiaMulMap_mul_w {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η : @RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f)}
    (φ : ξ ⟶ η) :
    (@RelativeInertia.hom _ (category f) _ _ _ _ _ φ).base ≫ (inertiaMulObj f η).mul =
      (inertiaMulObj f ξ).mul :=
  sorry

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The arrow map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulMap {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η : @RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f)}
    (φ : ξ ⟶ η) :
    ProductHom (inertiaMulObj f ξ) (inertiaMulObj f η) where
  pic := @RelativeInertia.hom _ (category f) _ _ _ _ _ φ
  mul_w := inertiaMulMap_mul_w f φ

set_option backward.privateInPublic true in
/-- The comparison on inertia arrows preserves identity morphisms. -/
private theorem inertiaMulMap_id {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f]
    (ξ : @RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f)) :
    inertiaMulMap f (𝟙 ξ) = ProductHom.id (inertiaMulObj f ξ) := by
  apply ProductHom.ext
  rfl

set_option backward.privateInPublic true in
/-- The comparison on inertia arrows preserves composition. -/
private theorem inertiaMulMap_comp {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η ζ : @RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f)}
    (φ : ξ ⟶ η) (ψ : η ⟶ ζ) :
    inertiaMulMap f (φ ≫ ψ) = ProductHom.comp (inertiaMulMap f φ) (inertiaMulMap f ψ) := by
  apply ProductHom.ext
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The total functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    @Functor (@RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f))
      (@RelativeInertia.category (Obj f) (category f) (Over S) inferInstance (p f))
      (ProductObj f) (productCategory f) :=
  @CategoryTheory.Functor.mk
    (@RelativeInertia (Obj f) (category f) (Over S) inferInstance (p f))
    (@RelativeInertia.category (Obj f) (category f) (Over S) inferInstance (p f))
    (ProductObj f) (productCategory f) (inertiaMulObj f) (inertiaMulMap f)
    (inertiaMulMap_id f) (inertiaMulMap_comp f)

set_option backward.privateInPublic true in
/-- The inertia comparison functor commutes with the projections to test schemes. -/
private theorem inertiaMulFunctor_w {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    @Functor.comp _
      (@RelativeInertia.category (Obj f) (category f) (Over S) inferInstance (p f))
      _ (productCategory f) _ inferInstance (inertiaMulFunctor f) (mulGroupProduct f).p =
      (StackOver.Groupoids.inertia (picardStack f)).p :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The based functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulBasedFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    (StackOver.Groupoids.inertia (picardStack f)).toBasedCategory ⥤ᵇ
      (mulGroupProduct f).toBasedCategory where
  toFunctor := inertiaMulFunctor f
  w := inertiaMulFunctor_w f

/-- The comparison 1-morphism from the inertia stack of `Pic_{X/S}` to
`𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulGroupHom {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    StackOver.Groupoids.inertia (picardStack f) ⟶ mulGroupProduct f :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (inertiaMulBasedFunctor f))

end AlgebraicGeometry.Picard

namespace AlgebraicGeometry

/-- Under the base-change structure-sheaf isomorphism hypothesis, the inertia of the Picard
stack is equivalent to the product of the relative multiplicative group and the Picard stack. -/
theorem inertia_mulGroupProduct {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    StackOver.Groupoids.Hom.IsEquivalence (Picard.inertiaMulGroupHom f) :=
  sorry

attribute [instance] inertia_mulGroupProduct

end AlgebraicGeometry
