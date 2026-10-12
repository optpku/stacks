/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedProduct.HomFamily
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant-target Hom equivalences for indexed products

For a `C`-valued presheaf `V` and `X : C`, the functor `homToConst V X` records the
degreewise morphisms `V.obj Delta ⟶ X`. A compatible family into the constant presheaf on
`X` is exactly a natural transformation from the indexing functor into this Hom functor.
Composing that identification with the indexed-product Hom-family universal property gives
the category-generic cotensor-Hom equivalence.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe w i d v u

namespace CategoryTheory.Functor

variable {D : Type i} [Category.{d} D] {C : Type u} [Category.{v} C]

/-- The type-valued functor of degreewise morphisms from a presheaf into a fixed object. -/
@[stacks 017M "constant-target mapping functor"]
abbrev homToConst (V : Dᵒᵖ ⥤ C) (X : C) : D ⥤ Type v :=
  V.rightOp ⋙ yoneda.obj X

namespace homToConst

/-- Precomposition in the source presheaf induces a morphism between constant-target mapping
functors. -/
@[stacks 017M "constant-target mapping functor source variance"]
def precomp {V₁ V₂ : Dᵒᵖ ⥤ C} (X : C) (f : V₁ ⟶ V₂) :
    Functor.homToConst V₂ X ⟶ Functor.homToConst V₁ X :=
  Functor.whiskerRight f.rightOp (yoneda.obj X)

/-- Evaluate source precomposition in a constant-target mapping functor. -/
@[simp, stacks 017M "constant-target mapping functor source variance formula"]
theorem precomp.app_apply {V₁ V₂ : Dᵒᵖ ⥤ C} (X : C) (f : V₁ ⟶ V₂)
    (Delta : D) (g : V₂.obj (Opposite.op Delta) ⟶ X) :
    (precomp X f).app Delta g = f.app (Opposite.op Delta) ≫ g := sorry

/-- Postcomposition in the target object induces a morphism between constant-target mapping
functors. -/
@[stacks 017M "constant-target mapping functor target variance"]
def postcomp (V : Dᵒᵖ ⥤ C) {X Y : C} (f : X ⟶ Y) :
    Functor.homToConst V X ⟶ Functor.homToConst V Y :=
  Functor.whiskerLeft V.rightOp (yoneda.map f)

/-- Evaluate target postcomposition in a constant-target mapping functor. -/
@[simp, stacks 017M "constant-target mapping functor target variance formula"]
theorem postcomp.app_apply (V : Dᵒᵖ ⥤ C) {X Y : C} (f : X ⟶ Y)
    (Delta : D) (g : V.obj (Opposite.op Delta) ⟶ X) :
    (postcomp V f).app Delta g = g ≫ f := sorry

/-- Evaluate the action of a constant-target mapping functor on an indexing morphism. -/
@[simp, stacks 017M "constant-target mapping functor index action"]
theorem map_apply (V : Dᵒᵖ ⥤ C) (X : C) {Delta Delta' : D}
    (f : Delta ⟶ Delta') (g : V.obj (Opposite.op Delta) ⟶ X) :
    (Functor.homToConst V X).map f g = V.map f.op ≫ g := sorry

end homToConst

namespace indexedProd.HomFamily

section ConstTarget

variable {U : D ⥤ Type v} {V : Dᵒᵖ ⥤ C} {X : C}

/-- The component of the natural transformation associated to a compatible family with
constant target. -/
@[stacks 017M "constant-target compatible family component"]
def toNatTrans.app
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) (Delta : D) :
    U.obj Delta ⟶ (Functor.homToConst V X).obj Delta :=
  TypeCat.ofHom fun x ↦ F.1 (Opposite.op Delta) x

/-- The components of a compatible family with constant target are natural in the index. -/
@[stacks 017M "constant-target compatible family naturality"]
theorem toNatTrans.naturality
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X))
    {Delta Delta' : D} (f : Delta ⟶ Delta') :
    U.map f ≫ toNatTrans.app F Delta' =
      toNatTrans.app F Delta ≫ (Functor.homToConst V X).map f := sorry

/-- A compatible indexed family with constant target determines a natural transformation to
the corresponding mapping functor. -/
@[stacks 017M "constant-target compatible family extraction"]
def toNatTrans (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    U ⟶ Functor.homToConst V X where
  app Delta := toNatTrans.app F Delta
  naturality := fun {_ _} f ↦ toNatTrans.naturality F f

/-- Evaluate the natural transformation extracted from a compatible constant-target family. -/
@[simp, stacks 017M "constant-target compatible family extraction formula"]
theorem toNatTrans.app_apply
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X))
    (Delta : D) (x : U.obj Delta) :
    (toNatTrans F).app Delta x = F.1 (Opposite.op Delta) x := sorry

/-- The Hom family underlying a natural transformation to a constant-target mapping functor. -/
@[stacks 017M "constant-target natural transformation family"]
def ofNatTrans (a : U ⟶ Functor.homToConst V X) :
    HomFamily U V ((Functor.const Dᵒᵖ).obj X) :=
  fun Delta x ↦ a.app (unop Delta) x

/-- Evaluate the Hom family underlying a constant-target natural transformation. -/
@[simp, stacks 017M "constant-target natural transformation family formula"]
theorem ofNatTrans.apply (a : U ⟶ Functor.homToConst V X)
    (Delta : Dᵒᵖ) (x : U.obj (unop Delta)) :
    ofNatTrans a Delta x = a.app (unop Delta) x := sorry

/-- The family underlying a natural transformation to a constant-target mapping functor is
compatible. -/
@[stacks 017M "constant-target natural transformation compatibility"]
theorem ofNatTrans.isCompatible (a : U ⟶ Functor.homToConst V X) :
    (ofNatTrans a).IsCompatible := sorry

/-- Package a natural transformation to a constant-target mapping functor as a compatible
indexed family. -/
@[stacks 017M "constant-target compatible family assembly"]
def ofNatTrans.compatible (a : U ⟶ Functor.homToConst V X) :
    Compatible U V ((Functor.const Dᵒᵖ).obj X) :=
  ⟨ofNatTrans a, ofNatTrans.isCompatible a⟩

/-- Evaluate the compatible family assembled from a constant-target natural transformation. -/
@[simp, stacks 017M "constant-target compatible family assembly formula"]
theorem ofNatTrans.compatible.apply (a : U ⟶ Functor.homToConst V X)
    (Delta : Dᵒᵖ) (x : U.obj (unop Delta)) :
    (ofNatTrans.compatible a).1 Delta x = a.app (unop Delta) x := sorry

/-- Extracting and then reassembling a compatible constant-target family is the identity. -/
@[stacks 017M "constant-target compatible family left inverse"]
theorem constEquiv.left_inv
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    ofNatTrans.compatible (toNatTrans F) = F := sorry

/-- Reassembling and then extracting a constant-target natural transformation is the identity. -/
@[stacks 017M "constant-target compatible family right inverse"]
theorem constEquiv.right_inv (a : U ⟶ Functor.homToConst V X) :
    toNatTrans (ofNatTrans.compatible a) = a := sorry

/-- Compatible Hom families with constant target are canonically natural transformations to
the corresponding mapping functor. -/
@[stacks 017M "constant-target compatible family equivalence"]
def constEquiv (U : D ⥤ Type v) (V : Dᵒᵖ ⥤ C) (X : C) :
    Compatible U V ((Functor.const Dᵒᵖ).obj X) ≃
      (U ⟶ Functor.homToConst V X) where
  toFun := toNatTrans
  invFun := ofNatTrans.compatible
  left_inv := constEquiv.left_inv
  right_inv := constEquiv.right_inv

/-- The forward map of `constEquiv` extracts the corresponding natural transformation. -/
@[simp, stacks 017M "constant-target compatible family equivalence forward formula"]
theorem constEquiv.apply
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    constEquiv U V X F = toNatTrans F := sorry

/-- The inverse map of `constEquiv` assembles the corresponding compatible family. -/
@[simp, stacks 017M "constant-target compatible family equivalence inverse formula"]
theorem constEquiv.symm_apply (a : U ⟶ Functor.homToConst V X) :
    (constEquiv U V X).symm a = ofNatTrans.compatible a := sorry

/-- The compatible-family constant-target equivalence is contravariantly natural in the
source presheaf. -/
@[stacks 017M "constant-target compatible family source naturality"]
theorem constEquiv.precomp {V₁ V₂ : Dᵒᵖ ⥤ C} (f : V₁ ⟶ V₂)
    (F : Compatible U V₂ ((Functor.const Dᵒᵖ).obj X)) :
    constEquiv U V₁ X
        (HomFamily.precompose.map (U := U)
          (W := (Functor.const Dᵒᵖ).obj X) f F) =
      constEquiv U V₂ X F ≫ Functor.homToConst.precomp X f := sorry

/-- The compatible-family constant-target equivalence is covariantly natural in the constant
object. -/
@[stacks 017M "constant-target compatible family object naturality"]
theorem constEquiv.postcomp {Y : C} (f : X ⟶ Y)
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    constEquiv U V Y
        (HomFamily.postcompose.map (U := U) (V := V)
          ((Functor.const Dᵒᵖ).map f) F) =
      constEquiv U V X F ≫ Functor.homToConst.postcomp V f := sorry

/-- The compatible-family constant-target equivalence is contravariantly natural in the
indexing functor. -/
@[stacks 017M "constant-target compatible family index naturality"]
theorem constEquiv.restrict {U₁ U₂ : D ⥤ Type v} (a : U₁ ⟶ U₂)
    (F : Compatible U₂ V ((Functor.const Dᵒᵖ).obj X)) :
    constEquiv U₁ V X
        (HomFamily.restrict.map (V := V)
          (W := (Functor.const Dᵒᵖ).obj X) a F) =
      a ≫ constEquiv U₂ V X F := sorry

end ConstTarget

section ConstTargetUlift

variable {U : D ⥤ Type w} {V : Dᵒᵖ ⥤ C} {X : C}

/-- The component of the universe-lifted natural transformation associated to a compatible
family with constant target. -/
@[stacks 017M "universe-lifted constant-target compatible family component"]
def toUliftNatTrans.app
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) (Delta : D) :
    (U ⋙ CategoryTheory.uliftFunctor.{v, w}).obj Delta ⟶
      (Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}).obj Delta :=
  TypeCat.ofHom fun x ↦ ULift.up (F.1 (Opposite.op Delta) x.down)

/-- The universe-lifted components of a compatible constant-target family are natural in the
indexing category. -/
@[stacks 017M "universe-lifted constant-target compatible family naturality"]
theorem toUliftNatTrans.naturality
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X))
    {Delta Delta' : D} (f : Delta ⟶ Delta') :
    (U ⋙ CategoryTheory.uliftFunctor.{v, w}).map f ≫
        toUliftNatTrans.app F Delta' =
      toUliftNatTrans.app F Delta ≫
        (Functor.homToConst V X ⋙
          CategoryTheory.uliftFunctor.{w, v}).map f := sorry

/-- A compatible constant-target family determines a natural transformation after lifting the
index and Hom universes to their common maximum. -/
@[stacks 017M "universe-lifted constant-target compatible family extraction"]
def toUliftNatTrans (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v} where
  app Delta := toUliftNatTrans.app F Delta
  naturality := fun {_ _} f ↦ toUliftNatTrans.naturality F f

/-- Evaluate the lifted natural transformation extracted from a compatible constant-target
family. -/
@[simp, stacks 017M "universe-lifted constant-target extraction formula"]
theorem toUliftNatTrans.app_apply
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X))
    (Delta : D) (x : ULift.{v} (U.obj Delta)) :
    (toUliftNatTrans F).app Delta x =
      ULift.up (F.1 (Opposite.op Delta) x.down) := sorry

/-- The Hom family obtained by removing the universe lifts from a natural transformation between
the lifted index and constant-target mapping functors. -/
@[stacks 017M "constant-target family from a universe-lifted natural transformation"]
def ofUliftNatTrans
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    HomFamily U V ((Functor.const Dᵒᵖ).obj X) :=
  fun Delta x ↦ (a.app (unop Delta) (ULift.up x)).down

/-- Evaluate the Hom family obtained from a lifted constant-target natural transformation. -/
@[simp, stacks 017M "constant-target family universe-lift removal formula"]
theorem ofUliftNatTrans.apply
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v})
    (Delta : Dᵒᵖ) (x : U.obj (unop Delta)) :
    ofUliftNatTrans a Delta x =
      (a.app (unop Delta) (ULift.up x)).down := sorry

/-- Removing the universe lifts from a natural transformation produces a compatible
constant-target Hom family. -/
@[stacks 017M "compatibility after removing constant-target universe lifts"]
theorem ofUliftNatTrans.isCompatible
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    (ofUliftNatTrans a).IsCompatible := sorry

/-- Package a natural transformation between the lifted index and mapping functors as a
compatible constant-target Hom family. -/
@[stacks 017M "compatible family from a universe-lifted natural transformation"]
def ofUliftNatTrans.compatible
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    Compatible U V ((Functor.const Dᵒᵖ).obj X) :=
  ⟨ofUliftNatTrans a, ofUliftNatTrans.isCompatible a⟩

/-- Evaluate the compatible family assembled from a lifted constant-target natural
transformation. -/
@[simp, stacks 017M "lifted constant-target compatible family assembly formula"]
theorem ofUliftNatTrans.compatible.apply
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v})
    (Delta : Dᵒᵖ) (x : U.obj (unop Delta)) :
    (ofUliftNatTrans.compatible a).1 Delta x =
      (a.app (unop Delta) (ULift.up x)).down := sorry

/-- Removing the lifts after extracting a lifted natural transformation recovers the original
compatible family. -/
@[stacks 017M "universe-lifted constant-target family left inverse"]
theorem constUliftEquiv.left_inv
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    ofUliftNatTrans.compatible (toUliftNatTrans F) = F := sorry

/-- Extracting a lifted natural transformation after removing its lifts recovers the original
natural transformation. -/
@[stacks 017M "universe-lifted constant-target family right inverse"]
theorem constUliftEquiv.right_inv
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    toUliftNatTrans (ofUliftNatTrans.compatible a) = a := sorry

/-- Compatible constant-target Hom families with an arbitrary index universe are canonically
natural transformations after lifting both sides to `Type (max w v)`. -/
@[stacks 017M "cross-universe constant-target compatible family equivalence"]
def constUliftEquiv (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C) (X : C) :
    Compatible U V ((Functor.const Dᵒᵖ).obj X) ≃
      (U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
        Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) where
  toFun := toUliftNatTrans
  invFun := ofUliftNatTrans.compatible
  left_inv := constUliftEquiv.left_inv
  right_inv := constUliftEquiv.right_inv

/-- The forward map of `constUliftEquiv` extracts the lifted natural transformation. -/
@[simp, stacks 017M "cross-universe constant-target family equivalence forward formula"]
theorem constUliftEquiv.apply
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    constUliftEquiv U V X F = toUliftNatTrans F := sorry

/-- The inverse map of `constUliftEquiv` removes the lifts and assembles a compatible family. -/
@[simp, stacks 017M "cross-universe constant-target family equivalence inverse formula"]
theorem constUliftEquiv.symm_apply
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    (constUliftEquiv U V X).symm a =
      ofUliftNatTrans.compatible a := sorry

/-- The lifted compatible-family constant-target equivalence is contravariantly natural in the
source presheaf. -/
@[stacks 017M "cross-universe constant-target compatible family source naturality"]
theorem constUliftEquiv.precomp {V₁ V₂ : Dᵒᵖ ⥤ C} (f : V₁ ⟶ V₂)
    (F : Compatible U V₂ ((Functor.const Dᵒᵖ).obj X)) :
    constUliftEquiv U V₁ X
        (HomFamily.precompose.map (U := U)
          (W := (Functor.const Dᵒᵖ).obj X) f F) =
      constUliftEquiv U V₂ X F ≫
        Functor.whiskerRight (Functor.homToConst.precomp X f)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The lifted compatible-family constant-target equivalence is covariantly natural in the
constant object. -/
@[stacks 017M "cross-universe constant-target compatible family object naturality"]
theorem constUliftEquiv.postcomp {Y : C} (f : X ⟶ Y)
    (F : Compatible U V ((Functor.const Dᵒᵖ).obj X)) :
    constUliftEquiv U V Y
        (HomFamily.postcompose.map (U := U) (V := V)
          ((Functor.const Dᵒᵖ).map f) F) =
      constUliftEquiv U V X F ≫
        Functor.whiskerRight (Functor.homToConst.postcomp V f)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The lifted compatible-family constant-target equivalence is contravariantly natural in the
indexing functor. -/
@[stacks 017M "cross-universe constant-target compatible family index naturality"]
theorem constUliftEquiv.restrict {U₁ U₂ : D ⥤ Type w} (a : U₁ ⟶ U₂)
    (F : Compatible U₂ V ((Functor.const Dᵒᵖ).obj X)) :
    constUliftEquiv U₁ V X
        (HomFamily.restrict.map (V := V)
          (W := (Functor.const Dᵒᵖ).obj X) a F) =
      Functor.whiskerRight a CategoryTheory.uliftFunctor.{v, w} ≫
        constUliftEquiv U₂ V X F := sorry

end ConstTargetUlift

end indexedProd.HomFamily

namespace indexedProd

namespace constHom

section ConstTarget

variable {U : D ⥤ Type v} {V : Dᵒᵖ ⥤ C} {X : C}

/-- Extract the constant-target natural transformation represented by a morphism into an
indexed product. -/
@[stacks 017M "indexed-product constant-target Hom extraction"]
def toNatTrans [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    U ⟶ Functor.homToConst V X :=
  HomFamily.toNatTrans (HomFamily.ofHom.compatible f)

/-- Evaluate the constant-target natural transformation extracted from an indexed-product
morphism. -/
@[simp, stacks 017M "indexed-product constant-target Hom extraction formula"]
theorem toNatTrans.app_apply [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X))
    (Delta : D) (x : U.obj Delta) :
    (toNatTrans f).app Delta x =
      f.app (Opposite.op Delta) ≫ Pi.π (fun _ : U.obj Delta ↦ X) x := sorry

/-- Assemble a morphism into a constant-target indexed product from the corresponding natural
transformation. -/
@[stacks 017M "indexed-product constant-target Hom assembly"]
def ofNatTrans [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⟶ Functor.homToConst V X) :
    V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X) :=
  HomFamily.toHom (HomFamily.ofNatTrans.compatible a)

/-- Projecting the indexed-product morphism assembled from a constant-target natural
transformation recovers its chosen component. -/
@[reassoc (attr := simp), stacks 017M "indexed-product constant-target Hom assembly formula"]
theorem ofNatTrans.app_π [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⟶ Functor.homToConst V X) (Delta : Dᵒᵖ)
    (x : U.obj (unop Delta)) :
    (ofNatTrans a).app Delta ≫
        Pi.π (fun _ : U.obj (unop Delta) ↦ X) x =
      a.app (unop Delta) x := sorry

/-- Assembling the natural transformation extracted from an indexed-product morphism recovers
that morphism. -/
@[stacks 017M "indexed-product constant-target Hom left inverse"]
theorem homEquiv.left_inv [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    ofNatTrans (toNatTrans f) = f := sorry

/-- Extracting the natural transformation from its assembled indexed-product morphism recovers
that natural transformation. -/
@[stacks 017M "indexed-product constant-target Hom right inverse"]
theorem homEquiv.right_inv [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⟶ Functor.homToConst V X) :
    toNatTrans (ofNatTrans a) = a := sorry

/-- Morphisms into an indexed product of a constant presheaf are canonically natural
transformations to the associated constant-target mapping functor. -/
@[stacks 017M "indexed-product constant-target Hom equivalence"]
def homEquiv (U : D ⥤ Type v) (V : Dᵒᵖ ⥤ C) (X : C)
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)] :
    (V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) ≃
      (U ⟶ Functor.homToConst V X) where
  toFun := toNatTrans
  invFun := ofNatTrans
  left_inv := homEquiv.left_inv
  right_inv := homEquiv.right_inv

/-- The forward map of `homEquiv` extracts the represented constant-target natural
transformation. -/
@[simp, stacks 017M "indexed-product constant-target Hom equivalence forward formula"]
theorem homEquiv.apply [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    homEquiv U V X f = toNatTrans f := sorry

/-- The inverse map of `homEquiv` assembles the represented indexed-product morphism. -/
@[simp, stacks 017M "indexed-product constant-target Hom equivalence inverse formula"]
theorem homEquiv.symm_apply [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⟶ Functor.homToConst V X) :
    (homEquiv U V X).symm a = ofNatTrans a := sorry

/-- The constant-target Hom equivalence is contravariantly natural under precomposition in its
source presheaf. -/
@[stacks 017M "indexed-product constant-target source naturality"]
theorem homEquiv.precomp {V₁ V₂ : Dᵒᵖ ⥤ C}
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    homEquiv U V₁ X (f ≫ g) =
      homEquiv U V₂ X g ≫
        Functor.homToConst.precomp X f := sorry

/-- The constant-target Hom equivalence is covariantly natural in the constant object. -/
@[stacks 017M "indexed-product constant-object naturality"]
theorem homEquiv.postcomp {Y : C}
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj Y)]
    (f : X ⟶ Y) (g : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    homEquiv U V Y
        (g ≫ indexedProd.hom U ((Functor.const Dᵒᵖ).map f)) =
      homEquiv U V X g ≫
        Functor.homToConst.postcomp V f := sorry

/-- The constant-target Hom equivalence is contravariantly natural in the indexing functor. -/
@[stacks 017M "indexed-product constant-target index naturality"]
theorem homEquiv.restrict {U₁ U₂ : D ⥤ Type v}
    [HasIndexedProd U₁ ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedProd U₂ ((Functor.const Dᵒᵖ).obj X)]
    (a : U₁ ⟶ U₂)
    (g : V ⟶ indexedProd U₂ ((Functor.const Dᵒᵖ).obj X)) :
    homEquiv U₁ V X
        (g ≫ indexedProd.indexHom ((Functor.const Dᵒᵖ).obj X) a) =
      a ≫ homEquiv U₂ V X g := sorry

end ConstTarget

section Ulift

variable {U : D ⥤ Type w} {V : Dᵒᵖ ⥤ C} {X : C}

/-- Extract the lifted constant-target natural transformation represented by a morphism into an
indexed product. -/
@[stacks 017M "cross-universe indexed-product Hom extraction"]
def toUliftNatTrans [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v} :=
  HomFamily.toUliftNatTrans (HomFamily.ofHom.compatible f)

/-- Evaluate the lifted constant-target natural transformation extracted from an
indexed-product morphism. -/
@[simp, stacks 017M "cross-universe indexed-product Hom extraction formula"]
theorem toUliftNatTrans.app_apply
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X))
    (Delta : D) (x : ULift.{v} (U.obj Delta)) :
    (toUliftNatTrans f).app Delta x =
      ULift.up (f.app (Opposite.op Delta) ≫
        Pi.π (fun _ : U.obj Delta ↦ X) x.down) := sorry

/-- Assemble a morphism into a constant-target indexed product from a natural transformation
between the corresponding lifted index and mapping functors. -/
@[stacks 017M "cross-universe indexed-product Hom assembly"]
def ofUliftNatTrans [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X) :=
  HomFamily.toHom (HomFamily.ofUliftNatTrans.compatible a)

/-- Projecting the indexed-product morphism assembled from a lifted constant-target natural
transformation recovers its chosen component after removing the lift. -/
@[reassoc (attr := simp), stacks 017M "cross-universe indexed-product Hom assembly formula"]
theorem ofUliftNatTrans.app_π
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v})
    (Delta : Dᵒᵖ) (x : U.obj (unop Delta)) :
    (ofUliftNatTrans a).app Delta ≫
        Pi.π (fun _ : U.obj (unop Delta) ↦ X) x =
      (a.app (unop Delta) (ULift.up x)).down := sorry

/-- Assembling the lifted natural transformation extracted from an indexed-product morphism
recovers that morphism. -/
@[stacks 017M "cross-universe indexed-product Hom left inverse"]
theorem uliftEquiv.left_inv [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    ofUliftNatTrans (toUliftNatTrans f) = f := sorry

/-- Extracting the lifted natural transformation from its assembled indexed-product morphism
recovers that natural transformation. -/
@[stacks 017M "cross-universe indexed-product Hom right inverse"]
theorem uliftEquiv.right_inv [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    toUliftNatTrans (ofUliftNatTrans a) = a := sorry

/-- Morphisms into a constant-target indexed product with an arbitrary index universe are
canonically natural transformations after lifting the index and Hom functors to a common
universe. -/
@[stacks 017M "cross-universe indexed-product constant-target Hom equivalence"]
def uliftEquiv (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C) (X : C)
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)] :
    (V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) ≃
      (U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
        Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) where
  toFun := toUliftNatTrans
  invFun := ofUliftNatTrans
  left_inv := uliftEquiv.left_inv
  right_inv := uliftEquiv.right_inv

/-- The forward map of `uliftEquiv` extracts the represented lifted natural transformation. -/
@[simp, stacks 017M "cross-universe indexed-product Hom equivalence forward formula"]
theorem uliftEquiv.apply [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    uliftEquiv U V X f = toUliftNatTrans f := sorry

/-- The inverse map of `uliftEquiv` assembles the represented indexed-product morphism. -/
@[simp, stacks 017M "cross-universe indexed-product Hom equivalence inverse formula"]
theorem uliftEquiv.symm_apply [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homToConst V X ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    (uliftEquiv U V X).symm a = ofUliftNatTrans a := sorry

/-- The cross-universe constant-target Hom equivalence is contravariantly natural under
precomposition in its source presheaf. -/
@[stacks 017M "cross-universe indexed-product source naturality"]
theorem uliftEquiv.precomp {V₁ V₂ : Dᵒᵖ ⥤ C}
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    uliftEquiv U V₁ X (f ≫ g) =
      uliftEquiv U V₂ X g ≫
        Functor.whiskerRight
          (Functor.homToConst.precomp X f)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe constant-target Hom equivalence is covariantly natural in the constant
object. -/
@[stacks 017M "cross-universe indexed-product constant-object naturality"]
theorem uliftEquiv.postcomp {Y : C}
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedProd U ((Functor.const Dᵒᵖ).obj Y)]
    (f : X ⟶ Y) (g : V ⟶ indexedProd U ((Functor.const Dᵒᵖ).obj X)) :
    uliftEquiv U V Y
        (g ≫ indexedProd.hom U ((Functor.const Dᵒᵖ).map f)) =
      uliftEquiv U V X g ≫
        Functor.whiskerRight
          (Functor.homToConst.postcomp V f)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe constant-target Hom equivalence is contravariantly natural in the
indexing functor. -/
@[stacks 017M "cross-universe indexed-product index naturality"]
theorem uliftEquiv.restrict {U₁ U₂ : D ⥤ Type w}
    [HasIndexedProd U₁ ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedProd U₂ ((Functor.const Dᵒᵖ).obj X)]
    (a : U₁ ⟶ U₂)
    (g : V ⟶ indexedProd U₂ ((Functor.const Dᵒᵖ).obj X)) :
    uliftEquiv U₁ V X
        (g ≫ indexedProd.indexHom ((Functor.const Dᵒᵖ).obj X) a) =
      Functor.whiskerRight a CategoryTheory.uliftFunctor.{v, w} ≫
        uliftEquiv U₂ V X g := sorry

end Ulift

end constHom

end indexedProd

end CategoryTheory.Functor
