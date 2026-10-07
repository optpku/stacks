module

public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant-source Hom equivalences for indexed coproducts

For a `C`-valued presheaf `W` and `X : C`, the functor `homFromConst X W` records the
degreewise morphisms `X ⟶ W.obj Delta`.  A compatible family from the constant presheaf on
`X` is exactly a natural transformation into this functor.  Composing that identification with
the indexed-coproduct Hom-family universal property gives the category-generic tensor-Hom
equivalence used by simplicial copowers.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe w i d v u

namespace CategoryTheory.Functor

variable {D : Type i} [Category.{d} D] {C : Type u} [Category.{v} C]

/-- The type-valued presheaf of degreewise morphisms from a fixed object into a
`C`-valued presheaf. -/
@[stacks 017D "constant-source mapping presheaf"]
abbrev homFromConst (X : C) (W : Dᵒᵖ ⥤ C) : Dᵒᵖ ⥤ Type v :=
  W ⋙ coyoneda.obj (op X)

namespace homFromConst

/-- Postcomposition in the target presheaf induces a morphism between constant-source mapping
presheaves. -/
@[stacks 017D "constant-source mapping presheaf target variance"]
def postcomp (X : C) {W₁ W₂ : Dᵒᵖ ⥤ C} (g : W₁ ⟶ W₂) :
    Functor.homFromConst X W₁ ⟶ Functor.homFromConst X W₂ :=
  Functor.whiskerRight g (coyoneda.obj (op X))

/-- Evaluate target postcomposition in a constant-source mapping presheaf. -/
@[simp, stacks 017D "constant-source mapping presheaf target variance formula"]
theorem postcomp.app_apply (X : C) {W₁ W₂ : Dᵒᵖ ⥤ C} (g : W₁ ⟶ W₂)
    (Delta : Dᵒᵖ) (f : X ⟶ W₁.obj Delta) :
    (postcomp X g).app Delta f = f ≫ g.app Delta := sorry

/-- Precomposition in the source object induces a morphism between constant-source mapping
presheaves. -/
@[stacks 017D "constant-source mapping presheaf source variance"]
def precomp (W : Dᵒᵖ ⥤ C) {X Y : C} (f : X ⟶ Y) :
    Functor.homFromConst Y W ⟶ Functor.homFromConst X W :=
  Functor.whiskerLeft W (coyoneda.map f.op)

/-- Evaluate source precomposition in a constant-source mapping presheaf. -/
@[simp, stacks 017D "constant-source mapping presheaf source variance formula"]
theorem precomp.app_apply (W : Dᵒᵖ ⥤ C) {X Y : C} (f : X ⟶ Y)
    (Delta : Dᵒᵖ) (g : Y ⟶ W.obj Delta) :
    (precomp W f).app Delta g = f ≫ g := sorry

/-- Evaluate the action of a constant-source mapping presheaf on an indexing morphism. -/
@[simp, stacks 017D "constant-source mapping presheaf index action"]
theorem map_apply (X : C) (W : Dᵒᵖ ⥤ C) {Delta Delta' : Dᵒᵖ}
    (f : Delta ⟶ Delta') (g : X ⟶ W.obj Delta) :
    (Functor.homFromConst X W).map f g = g ≫ W.map f := sorry

end homFromConst

namespace indexedCoprod.HomFamily

section ConstSource

variable {U : Dᵒᵖ ⥤ Type v} {X : C} {W : Dᵒᵖ ⥤ C}

/-- The component of the natural transformation associated to a compatible family with
constant source. -/
@[stacks 017D "constant-source compatible family component"]
def toNatTrans.app
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) (Delta : Dᵒᵖ) :
    U.obj Delta ⟶ (Functor.homFromConst X W).obj Delta :=
  TypeCat.ofHom (F.1 Delta)

/-- The components of a compatible family with constant source are natural in the index. -/
@[stacks 017D "constant-source compatible family naturality"]
theorem toNatTrans.naturality
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W)
    {Delta Delta' : Dᵒᵖ} (f : Delta ⟶ Delta') :
    U.map f ≫ toNatTrans.app F Delta' =
      toNatTrans.app F Delta ≫ (Functor.homFromConst X W).map f := sorry

/-- A compatible indexed family with constant source determines a natural transformation into
the corresponding mapping presheaf. -/
@[stacks 017D "constant-source compatible family extraction"]
def toNatTrans (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) :
    U ⟶ Functor.homFromConst X W where
  app Delta := toNatTrans.app F Delta
  naturality := fun {_ _} f ↦ toNatTrans.naturality F f

/-- Evaluate the natural transformation extracted from a compatible constant-source family. -/
@[simp, stacks 017D "constant-source compatible family extraction formula"]
theorem toNatTrans.app_apply
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W)
    (Delta : Dᵒᵖ) (x : U.obj Delta) :
    (toNatTrans F).app Delta x = F.1 Delta x := sorry

/-- The Hom family underlying a natural transformation into a constant-source mapping
presheaf. -/
@[stacks 017D "constant-source natural transformation family"]
def ofNatTrans (a : U ⟶ Functor.homFromConst X W) :
    HomFamily U ((Functor.const Dᵒᵖ).obj X) W :=
  fun Delta x ↦ a.app Delta x

/-- Evaluate the Hom family underlying a constant-source natural transformation. -/
@[simp, stacks 017D "constant-source natural transformation family formula"]
theorem ofNatTrans.apply (a : U ⟶ Functor.homFromConst X W)
    (Delta : Dᵒᵖ) (x : U.obj Delta) :
    ofNatTrans a Delta x = a.app Delta x := sorry

/-- The family underlying a natural transformation into a constant-source mapping presheaf is
compatible. -/
@[stacks 017D "constant-source natural transformation compatibility"]
theorem ofNatTrans.isCompatible (a : U ⟶ Functor.homFromConst X W) :
    (ofNatTrans a).IsCompatible := sorry

/-- Package a natural transformation into a constant-source mapping presheaf as a compatible
indexed family. -/
@[stacks 017D "constant-source compatible family assembly"]
def ofNatTrans.compatible (a : U ⟶ Functor.homFromConst X W) :
    Compatible U ((Functor.const Dᵒᵖ).obj X) W :=
  ⟨ofNatTrans a, ofNatTrans.isCompatible a⟩

/-- Evaluate the compatible family assembled from a constant-source natural transformation. -/
@[simp, stacks 017D "constant-source compatible family assembly formula"]
theorem ofNatTrans.compatible.apply (a : U ⟶ Functor.homFromConst X W)
    (Delta : Dᵒᵖ) (x : U.obj Delta) :
    (ofNatTrans.compatible a).1 Delta x = a.app Delta x := sorry

/-- Extracting and then reassembling a compatible constant-source family is the identity. -/
@[stacks 017D]
theorem constEquiv.left_inv
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) :
    ofNatTrans.compatible (toNatTrans F) = F := sorry

/-- Reassembling and then extracting a constant-source natural transformation is the identity. -/
@[stacks 017D]
theorem constEquiv.right_inv (a : U ⟶ Functor.homFromConst X W) :
    toNatTrans (ofNatTrans.compatible a) = a := sorry

/-- Compatible Hom families with constant source are canonically natural transformations into
the corresponding mapping presheaf. -/
@[stacks 017D "constant-source compatible family equivalence"]
def constEquiv (U : Dᵒᵖ ⥤ Type v) (X : C) (W : Dᵒᵖ ⥤ C) :
    Compatible U ((Functor.const Dᵒᵖ).obj X) W ≃
      (U ⟶ Functor.homFromConst X W) where
  toFun := toNatTrans
  invFun := ofNatTrans.compatible
  left_inv := constEquiv.left_inv
  right_inv := constEquiv.right_inv

/-- The forward map of `constEquiv` extracts the corresponding natural transformation. -/
@[simp, stacks 017D "constant-source compatible family equivalence forward formula"]
theorem constEquiv.apply
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) :
    constEquiv U X W F = toNatTrans F := sorry

/-- The inverse map of `constEquiv` assembles the corresponding compatible family. -/
@[simp, stacks 017D "constant-source compatible family equivalence inverse formula"]
theorem constEquiv.symm_apply (a : U ⟶ Functor.homFromConst X W) :
    (constEquiv U X W).symm a = ofNatTrans.compatible a := sorry

/-- The compatible-family constant-source equivalence is covariantly natural in the target
presheaf. -/
@[stacks 017D "constant-source compatible family target naturality"]
theorem constEquiv.postcomp {W₁ W₂ : Dᵒᵖ ⥤ C} (g : W₁ ⟶ W₂)
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W₁) :
    constEquiv U X W₂
        (HomFamily.postcompose.map (U := U)
          (V := (Functor.const Dᵒᵖ).obj X) g F) =
      constEquiv U X W₁ F ≫ Functor.homFromConst.postcomp X g := sorry

/-- The compatible-family constant-source equivalence is contravariantly natural in the
constant object. -/
@[stacks 017D "constant-source compatible family object naturality"]
theorem constEquiv.precomp {Y : C} (f : X ⟶ Y)
    (F : Compatible U ((Functor.const Dᵒᵖ).obj Y) W) :
    constEquiv U X W
        (HomFamily.precompose.map (U := U) (W := W)
          ((Functor.const Dᵒᵖ).map f) F) =
      constEquiv U Y W F ≫ Functor.homFromConst.precomp W f := sorry

/-- The compatible-family constant-source equivalence is contravariantly natural in the
indexing presheaf. -/
@[stacks 017D "constant-source compatible family index naturality"]
theorem constEquiv.restrict {U₁ U₂ : Dᵒᵖ ⥤ Type v} (a : U₁ ⟶ U₂)
    (F : Compatible U₂ ((Functor.const Dᵒᵖ).obj X) W) :
    constEquiv U₁ X W
        (HomFamily.restrict.map (V := (Functor.const Dᵒᵖ).obj X)
          (W := W) a F) =
      a ≫ constEquiv U₂ X W F := sorry

end ConstSource

section ConstSourceUlift

variable {U : Dᵒᵖ ⥤ Type w} {X : C} {W : Dᵒᵖ ⥤ C}

/-- The component of the universe-lifted natural transformation associated to a compatible
family with constant source. -/
@[stacks 017D "universe-lifted constant-source compatible family component"]
def toUliftNatTrans.app
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) (Delta : Dᵒᵖ) :
    (U ⋙ CategoryTheory.uliftFunctor.{v, w}).obj Delta ⟶
      (Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}).obj Delta :=
  TypeCat.ofHom fun x ↦ ULift.up (F.1 Delta x.down)

/-- The universe-lifted components of a compatible constant-source family are natural in the
indexing category. -/
@[stacks 017D "universe-lifted constant-source compatible family naturality"]
theorem toUliftNatTrans.naturality
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W)
    {Delta Delta' : Dᵒᵖ} (f : Delta ⟶ Delta') :
    (U ⋙ CategoryTheory.uliftFunctor.{v, w}).map f ≫
        toUliftNatTrans.app F Delta' =
      toUliftNatTrans.app F Delta ≫
        (Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}).map f := sorry

/-- A compatible constant-source family determines a natural transformation after lifting the
index and Hom universes to their common maximum. -/
@[stacks 017D "universe-lifted constant-source compatible family extraction"]
def toUliftNatTrans (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) :
    U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v} where
  app Delta := toUliftNatTrans.app F Delta
  naturality := fun {_ _} f ↦ toUliftNatTrans.naturality F f

/-- Evaluate the lifted natural transformation extracted from a compatible constant-source
family. -/
@[simp, stacks 017D "universe-lifted constant-source extraction formula"]
theorem toUliftNatTrans.app_apply
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W)
    (Delta : Dᵒᵖ) (x : ULift.{v} (U.obj Delta)) :
    (toUliftNatTrans F).app Delta x = ULift.up (F.1 Delta x.down) := sorry

/-- The Hom family obtained by removing the universe lifts from a natural transformation between
the lifted index and constant-source mapping presheaves. -/
@[stacks 017D "constant-source family from a universe-lifted natural transformation"]
def ofUliftNatTrans
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    HomFamily U ((Functor.const Dᵒᵖ).obj X) W :=
  fun Delta x ↦ (a.app Delta (ULift.up x)).down

/-- Evaluate the Hom family obtained from a lifted constant-source natural transformation. -/
@[simp, stacks 017D "constant-source family universe-lift removal formula"]
theorem ofUliftNatTrans.apply
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v})
    (Delta : Dᵒᵖ) (x : U.obj Delta) :
    ofUliftNatTrans a Delta x = (a.app Delta (ULift.up x)).down := sorry

/-- Removing the universe lifts from a natural transformation produces a compatible
constant-source Hom family. -/
@[stacks 017D "compatibility after removing constant-source universe lifts"]
theorem ofUliftNatTrans.isCompatible
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    (ofUliftNatTrans a).IsCompatible := sorry

/-- Package a natural transformation between the lifted index and mapping presheaves as a
compatible constant-source Hom family. -/
@[stacks 017D "compatible family from a universe-lifted natural transformation"]
def ofUliftNatTrans.compatible
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    Compatible U ((Functor.const Dᵒᵖ).obj X) W :=
  ⟨ofUliftNatTrans a, ofUliftNatTrans.isCompatible a⟩

/-- Evaluate the compatible family assembled from a lifted constant-source natural
transformation. -/
@[simp, stacks 017D "lifted constant-source compatible family assembly formula"]
theorem ofUliftNatTrans.compatible.apply
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v})
    (Delta : Dᵒᵖ) (x : U.obj Delta) :
    (ofUliftNatTrans.compatible a).1 Delta x =
      (a.app Delta (ULift.up x)).down := sorry

/-- Removing the lifts after extracting a lifted natural transformation recovers the original
compatible family. -/
@[stacks 017D "universe-lifted constant-source family left inverse"]
theorem constUliftEquiv.left_inv
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) :
    ofUliftNatTrans.compatible (toUliftNatTrans F) = F := sorry

/-- Extracting a lifted natural transformation after removing its lifts recovers the original
natural transformation. -/
@[stacks 017D "universe-lifted constant-source family right inverse"]
theorem constUliftEquiv.right_inv
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    toUliftNatTrans (ofUliftNatTrans.compatible a) = a := sorry

/-- Compatible constant-source Hom families with an arbitrary index universe are canonically
natural transformations after lifting both sides to `Type (max w v)`. -/
@[stacks 017D "cross-universe constant-source compatible family equivalence"]
def constUliftEquiv (U : Dᵒᵖ ⥤ Type w) (X : C) (W : Dᵒᵖ ⥤ C) :
    Compatible U ((Functor.const Dᵒᵖ).obj X) W ≃
      (U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
        Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) where
  toFun := toUliftNatTrans
  invFun := ofUliftNatTrans.compatible
  left_inv := constUliftEquiv.left_inv
  right_inv := constUliftEquiv.right_inv

/-- The forward map of `constUliftEquiv` extracts the lifted natural transformation. -/
@[simp, stacks 017D "cross-universe constant-source family equivalence forward formula"]
theorem constUliftEquiv.apply
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W) :
    constUliftEquiv U X W F = toUliftNatTrans F := sorry

/-- The inverse map of `constUliftEquiv` removes the lifts and assembles a compatible family. -/
@[simp, stacks 017D "cross-universe constant-source family equivalence inverse formula"]
theorem constUliftEquiv.symm_apply
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    (constUliftEquiv U X W).symm a =
      ofUliftNatTrans.compatible a := sorry

/-- The lifted compatible-family constant-source equivalence is covariantly natural in the
target presheaf. -/
@[stacks 017D "cross-universe constant-source compatible family target naturality"]
theorem constUliftEquiv.postcomp {W₁ W₂ : Dᵒᵖ ⥤ C} (g : W₁ ⟶ W₂)
    (F : Compatible U ((Functor.const Dᵒᵖ).obj X) W₁) :
    constUliftEquiv U X W₂
        (HomFamily.postcompose.map (U := U)
          (V := (Functor.const Dᵒᵖ).obj X) g F) =
      constUliftEquiv U X W₁ F ≫
        Functor.whiskerRight (Functor.homFromConst.postcomp X g)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The lifted compatible-family constant-source equivalence is contravariantly natural in the
constant object. -/
@[stacks 017D "cross-universe constant-source compatible family object naturality"]
theorem constUliftEquiv.precomp {Y : C} (f : X ⟶ Y)
    (F : Compatible U ((Functor.const Dᵒᵖ).obj Y) W) :
    constUliftEquiv U X W
        (HomFamily.precompose.map (U := U) (W := W)
          ((Functor.const Dᵒᵖ).map f) F) =
      constUliftEquiv U Y W F ≫
        Functor.whiskerRight (Functor.homFromConst.precomp W f)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The lifted compatible-family constant-source equivalence is contravariantly natural in the
indexing presheaf. -/
@[stacks 017D "cross-universe constant-source compatible family index naturality"]
theorem constUliftEquiv.restrict {U₁ U₂ : Dᵒᵖ ⥤ Type w} (a : U₁ ⟶ U₂)
    (F : Compatible U₂ ((Functor.const Dᵒᵖ).obj X) W) :
    constUliftEquiv U₁ X W
        (HomFamily.restrict.map (V := (Functor.const Dᵒᵖ).obj X)
          (W := W) a F) =
      Functor.whiskerRight a CategoryTheory.uliftFunctor.{v, w} ≫
        constUliftEquiv U₂ X W F := sorry

end ConstSourceUlift

end indexedCoprod.HomFamily

namespace indexedCoprod

namespace constHom

section ConstSource

variable {U : Dᵒᵖ ⥤ Type v} {X : C} {W : Dᵒᵖ ⥤ C}

/-- Extract the constant-source natural transformation represented by a morphism from an
indexed coproduct. -/
@[stacks 017D "indexed-coproduct constant-source Hom extraction"]
def toNatTrans [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W) :
    U ⟶ Functor.homFromConst X W :=
  HomFamily.toNatTrans (HomFamily.ofHom.compatible f)

/-- Evaluate the constant-source natural transformation extracted from an indexed-coproduct
morphism. -/
@[simp, stacks 017D "indexed-coproduct constant-source Hom extraction formula"]
theorem toNatTrans.app_apply [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W)
    (Delta : Dᵒᵖ) (x : U.obj Delta) :
    (toNatTrans f).app Delta x =
      Sigma.ι (fun _ : U.obj Delta ↦ X) x ≫ f.app Delta := sorry

/-- Assemble a morphism from a constant-source indexed coproduct from the corresponding natural
transformation. -/
@[stacks 017D "indexed-coproduct constant-source Hom assembly"]
def ofNatTrans [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⟶ Functor.homFromConst X W) :
    indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W :=
  HomFamily.toHom (HomFamily.ofNatTrans.compatible a)

/-- Restricting the indexed-coproduct morphism assembled from a constant-source natural
transformation to one summand recovers its chosen component. -/
@[reassoc (attr := simp), stacks 017D "indexed-coproduct constant-source Hom assembly formula"]
theorem ofNatTrans.ι_app [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⟶ Functor.homFromConst X W) (Delta : Dᵒᵖ) (x : U.obj Delta) :
    Sigma.ι (fun _ : U.obj Delta ↦ X) x ≫
        (ofNatTrans a).app Delta =
      a.app Delta x := sorry

/-- Morphisms from an indexed coproduct of a constant presheaf are canonically natural
transformations into the associated constant-source mapping presheaf. -/
@[stacks 017D "indexed-coproduct constant-source Hom equivalence"]
def homEquiv (U : Dᵒᵖ ⥤ Type v) (X : C) (W : Dᵒᵖ ⥤ C)
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)] :
    (indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W) ≃
      (U ⟶ Functor.homFromConst X W) :=
  (HomFamily.homEquiv U ((Functor.const Dᵒᵖ).obj X) W).trans
    (HomFamily.constEquiv U X W)

/-- The forward map of `homEquiv` extracts the represented constant-source natural
transformation. -/
@[simp, stacks 017D "indexed-coproduct constant-source Hom equivalence forward formula"]
theorem homEquiv.apply [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W) :
    homEquiv U X W f = toNatTrans f := sorry

/-- The inverse map of `homEquiv` assembles the represented indexed-coproduct morphism. -/
@[simp, stacks 017D "indexed-coproduct constant-source Hom equivalence inverse formula"]
theorem homEquiv.symm_apply [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⟶ Functor.homFromConst X W) :
    (homEquiv U X W).symm a = ofNatTrans a := sorry

/-- The generic constant-source Hom equivalence is natural under postcomposition in its
target presheaf. -/
@[stacks 017D "indexed-coproduct constant-source target naturality"]
theorem homEquiv.postcomp {W₁ W₂ : Dᵒᵖ ⥤ C}
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W₁) (g : W₁ ⟶ W₂) :
    homEquiv U X W₂ (f ≫ g) =
      homEquiv U X W₁ f ≫
        Functor.homFromConst.postcomp X g := sorry

/-- The generic constant-source Hom equivalence is contravariantly natural in the constant
object. -/
@[stacks 017D "indexed-coproduct constant-object naturality"]
theorem homEquiv.precomp {Y : C}
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj Y)]
    (f : X ⟶ Y) (g : indexedCoprod U ((Functor.const Dᵒᵖ).obj Y) ⟶ W) :
    homEquiv U X W
        (indexedCoprod.hom U ((Functor.const Dᵒᵖ).map f) ≫ g) =
      homEquiv U Y W g ≫
        Functor.homFromConst.precomp W f := sorry

/-- The generic constant-source Hom equivalence is contravariantly natural in the indexing
presheaf. -/
@[stacks 017D "indexed-coproduct constant-source index naturality"]
theorem homEquiv.restrict {U₁ U₂ : Dᵒᵖ ⥤ Type v}
    [HasIndexedCoprod U₁ ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedCoprod U₂ ((Functor.const Dᵒᵖ).obj X)]
    (a : U₁ ⟶ U₂)
    (f : indexedCoprod U₂ ((Functor.const Dᵒᵖ).obj X) ⟶ W) :
    homEquiv U₁ X W
        (indexedCoprod.indexHom ((Functor.const Dᵒᵖ).obj X) a ≫ f) =
      a ≫ homEquiv U₂ X W f := sorry

end ConstSource

section Ulift

variable {U : Dᵒᵖ ⥤ Type w} {X : C} {W : Dᵒᵖ ⥤ C}

/-- Extract the lifted constant-source natural transformation represented by a morphism from an
indexed coproduct. -/
@[stacks 017D "cross-universe indexed-coproduct Hom extraction"]
def toUliftNatTrans [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W) :
    U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v} :=
  HomFamily.toUliftNatTrans (HomFamily.ofHom.compatible f)

/-- Evaluate the lifted constant-source natural transformation extracted from an
indexed-coproduct morphism. -/
@[simp, stacks 017D "cross-universe indexed-coproduct Hom extraction formula"]
theorem toUliftNatTrans.app_apply
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W)
    (Delta : Dᵒᵖ) (x : ULift.{v} (U.obj Delta)) :
    (toUliftNatTrans f).app Delta x =
      ULift.up (Sigma.ι (fun _ : U.obj Delta ↦ X) x.down ≫ f.app Delta) := sorry

/-- Assemble a morphism from a constant-source indexed coproduct from a natural transformation
between the corresponding lifted index and mapping presheaves. -/
@[stacks 017D "cross-universe indexed-coproduct Hom assembly"]
def ofUliftNatTrans [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W :=
  HomFamily.toHom (HomFamily.ofUliftNatTrans.compatible a)

/-- Restricting the indexed-coproduct morphism assembled from a lifted constant-source natural
transformation to one summand recovers its chosen component after removing the lift. -/
@[reassoc (attr := simp), stacks 017D "cross-universe indexed-coproduct Hom assembly formula"]
theorem ofUliftNatTrans.ι_app
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v})
    (Delta : Dᵒᵖ) (x : U.obj Delta) :
    Sigma.ι (fun _ : U.obj Delta ↦ X) x ≫
        (ofUliftNatTrans a).app Delta =
      (a.app Delta (ULift.up x)).down := sorry

/-- Assembling the lifted natural transformation extracted from an indexed-coproduct morphism
recovers that morphism. -/
@[stacks 017D "cross-universe indexed-coproduct Hom left inverse"]
theorem uliftEquiv.left_inv [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W) :
    ofUliftNatTrans (toUliftNatTrans f) = f := sorry

/-- Extracting the lifted natural transformation from its assembled indexed-coproduct morphism
recovers that natural transformation. -/
@[stacks 017D "cross-universe indexed-coproduct Hom right inverse"]
theorem uliftEquiv.right_inv [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    toUliftNatTrans (ofUliftNatTrans a) = a := sorry

/-- Morphisms from a constant-source indexed coproduct with an arbitrary index universe are
canonically natural transformations after lifting the index and Hom presheaves to a common
universe. -/
@[stacks 017D "cross-universe indexed-coproduct constant-source Hom equivalence"]
def uliftEquiv (U : Dᵒᵖ ⥤ Type w) (X : C) (W : Dᵒᵖ ⥤ C)
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)] :
    (indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W) ≃
      (U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
        Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) where
  toFun := toUliftNatTrans
  invFun := ofUliftNatTrans
  left_inv := uliftEquiv.left_inv
  right_inv := uliftEquiv.right_inv

/-- The forward map of `uliftEquiv` extracts the represented lifted natural transformation. -/
@[simp, stacks 017D "cross-universe indexed-coproduct Hom equivalence forward formula"]
theorem uliftEquiv.apply [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W) :
    uliftEquiv U X W f = toUliftNatTrans f := sorry

/-- The inverse map of `uliftEquiv` assembles the represented indexed-coproduct morphism. -/
@[simp, stacks 017D "cross-universe indexed-coproduct Hom equivalence inverse formula"]
theorem uliftEquiv.symm_apply [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (a : U ⋙ CategoryTheory.uliftFunctor.{v, w} ⟶
      Functor.homFromConst X W ⋙ CategoryTheory.uliftFunctor.{w, v}) :
    (uliftEquiv U X W).symm a = ofUliftNatTrans a := sorry

/-- The cross-universe constant-source Hom equivalence is natural under postcomposition in the
target presheaf. -/
@[stacks 017D "cross-universe indexed-coproduct target naturality"]
theorem uliftEquiv.postcomp {W₁ W₂ : Dᵒᵖ ⥤ C}
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    (f : indexedCoprod U ((Functor.const Dᵒᵖ).obj X) ⟶ W₁) (g : W₁ ⟶ W₂) :
    uliftEquiv U X W₂ (f ≫ g) =
      uliftEquiv U X W₁ f ≫
        Functor.whiskerRight
          (Functor.homFromConst.postcomp X g)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe constant-source Hom equivalence is contravariantly natural in the
constant object. -/
@[stacks 017D "cross-universe indexed-coproduct constant-object naturality"]
theorem uliftEquiv.precomp {Y : C}
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedCoprod U ((Functor.const Dᵒᵖ).obj Y)]
    (f : X ⟶ Y) (g : indexedCoprod U ((Functor.const Dᵒᵖ).obj Y) ⟶ W) :
    uliftEquiv U X W
        (indexedCoprod.hom U ((Functor.const Dᵒᵖ).map f) ≫ g) =
      uliftEquiv U Y W g ≫
        Functor.whiskerRight
          (Functor.homFromConst.precomp W f)
          CategoryTheory.uliftFunctor.{w, v} := sorry

/-- The cross-universe constant-source Hom equivalence is contravariantly natural in the
indexing presheaf. -/
@[stacks 017D "cross-universe indexed-coproduct index naturality"]
theorem uliftEquiv.restrict {U₁ U₂ : Dᵒᵖ ⥤ Type w}
    [HasIndexedCoprod U₁ ((Functor.const Dᵒᵖ).obj X)]
    [HasIndexedCoprod U₂ ((Functor.const Dᵒᵖ).obj X)]
    (a : U₁ ⟶ U₂)
    (f : indexedCoprod U₂ ((Functor.const Dᵒᵖ).obj X) ⟶ W) :
    uliftEquiv U₁ X W
        (indexedCoprod.indexHom ((Functor.const Dᵒᵖ).obj X) a ≫ f) =
      Functor.whiskerRight a CategoryTheory.uliftFunctor.{v, w} ≫
        uliftEquiv U₂ X W f := sorry

end Ulift

end constHom

end indexedCoprod

end CategoryTheory.Functor
