/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedProduct.Functoriality
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatible families for indexed products

For an indexing functor `U : D ⥤ Type w` and `C`-valued presheaves `V` and `W`, this
module packages compatible degreewise families of maps from `V` to `W` indexed by `U`.
When `indexedProd U W` exists, such families are represented by the indexed product.

This is the category-generic universal-property owner underlying projection-family
constructions for indexed products.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe w i d v u

namespace CategoryTheory.Functor

variable {D : Type i} [Category.{d} D] {C : Type u} [Category.{v} C]

namespace indexedProd

section Families

variable (U : D ⥤ Type w) (V W : Dᵒᵖ ⥤ C)

/-- A degreewise family of morphisms from `V` to `W`, indexed by the elements of `U`. -/
@[stacks 0B15 "indexed-product Hom families"]
abbrev HomFamily :=
  ∀ Delta : Dᵒᵖ, U.obj (unop Delta) → (V.obj Delta ⟶ W.obj Delta)

namespace HomFamily

/-- Compatibility of an indexed degreewise Hom family with the presheaf structure maps. -/
@[stacks 0B15 "compatibility of indexed-product morphism families"]
def IsCompatible {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    (F : HomFamily U V W) : Prop :=
  ∀ ⦃Delta Delta' : Dᵒᵖ⦄ (f : Delta ⟶ Delta') (u : U.obj (unop Delta')),
    V.map f ≫ F Delta' u = F Delta (U.map f.unop u) ≫ W.map f

/-- A family is compatible precisely when it satisfies the displayed naturality equations. -/
@[stacks 0B15 "indexed-product compatibility equations"]
theorem isCompatible_iff {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    (F : HomFamily U V W) :
    F.IsCompatible ↔
      ∀ ⦃Delta Delta' : Dᵒᵖ⦄ (f : Delta ⟶ Delta')
          (u : U.obj (unop Delta')),
        V.map f ≫ F Delta' u = F Delta (U.map f.unop u) ≫ W.map f := sorry

/-- Compatible degreewise families of morphisms indexed by `U`. -/
@[stacks 0B15 "compatible indexed-product morphism families"]
abbrev Compatible :=
  { F : HomFamily U V W // F.IsCompatible }

end HomFamily

end Families

section TargetVariable

/-- Postcompose every component of a compatible family with a morphism of target presheaves. -/
@[stacks 0B15 "postcomposition of compatible indexed-product families"]
def HomFamily.postcompose {U : D ⥤ Type w} {V W W' : Dᵒᵖ ⥤ C}
    (g : W ⟶ W') (F : HomFamily.Compatible U V W) :
    HomFamily U V W' :=
  fun Delta u ↦ F.1 Delta u ≫ g.app Delta

/-- Evaluate target postcomposition at one degree and one index. -/
@[simp, stacks 0B15 "target postcomposition component"]
theorem HomFamily.postcompose.apply {U : D ⥤ Type w}
    {V W W' : Dᵒᵖ ⥤ C} (g : W ⟶ W')
    (F : HomFamily.Compatible U V W) (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    HomFamily.postcompose g F Delta u = F.1 Delta u ≫ g.app Delta := sorry

/-- Postcomposition preserves compatibility of indexed degreewise families. -/
@[stacks 0B15 "postcomposition preserves indexed-product compatibility"]
theorem HomFamily.postcompose.isCompatible {U : D ⥤ Type w}
    {V W W' : Dᵒᵖ ⥤ C} (g : W ⟶ W')
    (F : HomFamily.Compatible U V W) :
    (HomFamily.postcompose g F).IsCompatible := sorry

/-- Postcomposition as a morphism between the corresponding types of compatible families. -/
@[stacks 0B15 "map on compatible indexed-product families"]
def HomFamily.postcompose.map {U : D ⥤ Type w} {V W W' : Dᵒᵖ ⥤ C}
    (g : W ⟶ W') :
    HomFamily.Compatible U V W ⟶ HomFamily.Compatible U V W' :=
  TypeCat.ofHom fun F =>
    ⟨HomFamily.postcompose g F, HomFamily.postcompose.isCompatible g F⟩

/-- Evaluate the bundled target-postcomposition map at one degree and one index. -/
@[simp, stacks 0B15 "bundled target postcomposition component"]
theorem HomFamily.postcompose.map.apply {U : D ⥤ Type w}
    {V W W' : Dᵒᵖ ⥤ C} (g : W ⟶ W')
    (F : HomFamily.Compatible U V W) (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    (HomFamily.postcompose.map g F).1 Delta u =
      F.1 Delta u ≫ g.app Delta := sorry

/-- Postcomposition by an identity induces the identity map on compatible families. -/
@[simp, stacks 0B15 "identity postcomposition on indexed-product families"]
theorem HomFamily.postcompose.map_id (U : D ⥤ Type w)
    (V W : Dᵒᵖ ⥤ C) :
    HomFamily.postcompose.map (U := U) (V := V) (𝟙 W) =
      𝟙 (HomFamily.Compatible U V W) := sorry

/-- Postcomposition of compatible families respects composition of target morphisms. -/
@[simp, stacks 0B15 "composition of postcomposition maps on indexed-product families"]
theorem HomFamily.postcompose.map_comp (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C)
    {W₁ W₂ W₃ : Dᵒᵖ ⥤ C} (g : W₁ ⟶ W₂) (h : W₂ ⟶ W₃) :
    HomFamily.postcompose.map (U := U) (V := V) (g ≫ h) =
      HomFamily.postcompose.map (U := U) (V := V) g ≫
        HomFamily.postcompose.map (U := U) (V := V) h := sorry

end TargetVariable

section SourceVariable

/-- Precompose every component of a compatible family with a morphism of source presheaves. -/
@[stacks 0B15 "precomposition of compatible indexed-product families"]
def HomFamily.precompose {U : D ⥤ Type w} {V₁ V₂ W : Dᵒᵖ ⥤ C}
    (f : V₁ ⟶ V₂) (F : HomFamily.Compatible U V₂ W) :
    HomFamily U V₁ W :=
  fun Delta u ↦ f.app Delta ≫ F.1 Delta u

/-- Evaluate source precomposition at one degree and one index. -/
@[simp, stacks 0B15 "source precomposition component"]
theorem HomFamily.precompose.apply {U : D ⥤ Type w}
    {V₁ V₂ W : Dᵒᵖ ⥤ C} (f : V₁ ⟶ V₂)
    (F : HomFamily.Compatible U V₂ W) (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    HomFamily.precompose f F Delta u = f.app Delta ≫ F.1 Delta u := sorry

/-- Precomposition preserves compatibility of indexed degreewise families. -/
@[stacks 0B15 "precomposition preserves indexed-product compatibility"]
theorem HomFamily.precompose.isCompatible {U : D ⥤ Type w}
    {V₁ V₂ W : Dᵒᵖ ⥤ C} (f : V₁ ⟶ V₂)
    (F : HomFamily.Compatible U V₂ W) :
    (HomFamily.precompose f F).IsCompatible := sorry

/-- Precomposition as a morphism between the corresponding types of compatible families. -/
@[stacks 0B15 "precomposition map on compatible indexed-product families"]
def HomFamily.precompose.map {U : D ⥤ Type w} {V₁ V₂ W : Dᵒᵖ ⥤ C}
    (f : V₁ ⟶ V₂) :
    HomFamily.Compatible U V₂ W ⟶ HomFamily.Compatible U V₁ W :=
  TypeCat.ofHom fun F =>
    ⟨HomFamily.precompose f F, HomFamily.precompose.isCompatible f F⟩

/-- Evaluate the bundled source-precomposition map at one degree and one index. -/
@[simp, stacks 0B15 "bundled source precomposition component"]
theorem HomFamily.precompose.map.apply {U : D ⥤ Type w}
    {V₁ V₂ W : Dᵒᵖ ⥤ C} (f : V₁ ⟶ V₂)
    (F : HomFamily.Compatible U V₂ W) (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    (HomFamily.precompose.map f F).1 Delta u =
      f.app Delta ≫ F.1 Delta u := sorry

/-- Precomposition by an identity induces the identity map on compatible families. -/
@[simp, stacks 0B15 "identity precomposition on indexed-product families"]
theorem HomFamily.precompose.map_id (U : D ⥤ Type w)
    (V W : Dᵒᵖ ⥤ C) :
    HomFamily.precompose.map (U := U) (W := W) (𝟙 V) =
      𝟙 (HomFamily.Compatible U V W) := sorry

/-- Precomposition reverses composition of source morphisms. -/
@[simp, stacks 0B15 "composition of precomposition maps on indexed-product families"]
theorem HomFamily.precompose.map_comp (U : D ⥤ Type w) (W : Dᵒᵖ ⥤ C)
    {V₁ V₂ V₃ : Dᵒᵖ ⥤ C} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) :
    HomFamily.precompose.map (U := U) (W := W) (f ≫ g) =
      HomFamily.precompose.map (U := U) (W := W) g ≫
        HomFamily.precompose.map (U := U) (W := W) f := sorry

/-- Compatible families as a contravariant functor of the source presheaf. -/
@[stacks 0B15 "compatible indexed-product Hom-family functor"]
def HomFamily.functor (U : D ⥤ Type w) (W : Dᵒᵖ ⥤ C) :
    (Dᵒᵖ ⥤ C)ᵒᵖ ⥤ Type (max i w v) where
  obj V := HomFamily.Compatible U V.unop W
  map f := HomFamily.precompose.map (U := U) (W := W) f.unop
  map_id V := HomFamily.precompose.map_id U V.unop W
  map_comp f g := HomFamily.precompose.map_comp U W g.unop f.unop

end SourceVariable

section IndexVariable

/-- Restrict a compatible family along a morphism of indexing functors. -/
@[stacks 0B15 "restriction of compatible indexed-product families"]
def HomFamily.restrict {U₁ U₂ : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    (a : U₁ ⟶ U₂) (F : HomFamily.Compatible U₂ V W) :
    HomFamily U₁ V W :=
  fun Delta u ↦ F.1 Delta (a.app (unop Delta) u)

/-- Evaluate index restriction at one degree and one index. -/
@[simp, stacks 0B15 "index restriction component"]
theorem HomFamily.restrict.apply {U₁ U₂ : D ⥤ Type w}
    {V W : Dᵒᵖ ⥤ C} (a : U₁ ⟶ U₂)
    (F : HomFamily.Compatible U₂ V W) (Delta : Dᵒᵖ) (u : U₁.obj (unop Delta)) :
    HomFamily.restrict a F Delta u = F.1 Delta (a.app (unop Delta) u) := sorry

/-- Restriction preserves compatibility of indexed degreewise families. -/
@[stacks 0B15 "restriction preserves indexed-product compatibility"]
theorem HomFamily.restrict.isCompatible {U₁ U₂ : D ⥤ Type w}
    {V W : Dᵒᵖ ⥤ C} (a : U₁ ⟶ U₂)
    (F : HomFamily.Compatible U₂ V W) :
    (HomFamily.restrict a F).IsCompatible := sorry

/-- Restriction as a morphism between the corresponding types of compatible families. -/
@[stacks 0B15 "restriction map on compatible indexed-product families"]
def HomFamily.restrict.map {U₁ U₂ : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    (a : U₁ ⟶ U₂) :
    HomFamily.Compatible U₂ V W ⟶ HomFamily.Compatible U₁ V W :=
  TypeCat.ofHom fun F =>
    ⟨HomFamily.restrict a F, HomFamily.restrict.isCompatible a F⟩

/-- Evaluate the bundled index-restriction map at one degree and one index. -/
@[simp, stacks 0B15 "bundled index restriction component"]
theorem HomFamily.restrict.map.apply {U₁ U₂ : D ⥤ Type w}
    {V W : Dᵒᵖ ⥤ C} (a : U₁ ⟶ U₂)
    (F : HomFamily.Compatible U₂ V W) (Delta : Dᵒᵖ) (u : U₁.obj (unop Delta)) :
    (HomFamily.restrict.map a F).1 Delta u =
      F.1 Delta (a.app (unop Delta) u) := sorry

/-- Restriction along an identity induces the identity map on compatible families. -/
@[simp, stacks 0B15 "identity restriction on indexed-product families"]
theorem HomFamily.restrict.map_id (U : D ⥤ Type w)
    (V W : Dᵒᵖ ⥤ C) :
    HomFamily.restrict.map (V := V) (W := W) (𝟙 U) =
      𝟙 (HomFamily.Compatible U V W) := sorry

/-- Restriction reverses composition of indexing-functor morphisms. -/
@[simp, stacks 0B15 "composition of restriction maps on indexed-product families"]
theorem HomFamily.restrict.map_comp (V W : Dᵒᵖ ⥤ C)
    {U₁ U₂ U₃ : D ⥤ Type w} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) :
    HomFamily.restrict.map (V := V) (W := W) (a ≫ b) =
      HomFamily.restrict.map (V := V) (W := W) b ≫
        HomFamily.restrict.map (V := V) (W := W) a := sorry

/-- Restriction along the inverse of an index isomorphism undoes restriction along its
forward map. -/
@[stacks 0B15 "index-isomorphism restriction left inverse"]
theorem HomFamily.restrict.left_inv {U₁ U₂ : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    (e : U₁ ≅ U₂) (F : HomFamily.Compatible U₂ V W) :
    HomFamily.restrict.map (V := V) (W := W) e.inv
        (HomFamily.restrict.map (V := V) (W := W) e.hom F) =
      F := sorry

/-- Restriction along an index isomorphism undoes restriction along its inverse. -/
@[stacks 0B15 "index-isomorphism restriction right inverse"]
theorem HomFamily.restrict.right_inv {U₁ U₂ : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    (e : U₁ ≅ U₂) (F : HomFamily.Compatible U₁ V W) :
    HomFamily.restrict.map (V := V) (W := W) e.hom
        (HomFamily.restrict.map (V := V) (W := W) e.inv F) =
      F := sorry

/-- An isomorphism of indexing diagrams induces an equivalence of compatible families, in
the contravariant direction of index restriction. -/
@[stacks 0B15 "compatible-family equivalence under index isomorphism"]
def HomFamily.restrictEquiv {U₁ U₂ : D ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : Dᵒᵖ ⥤ C) :
    HomFamily.Compatible U₂ V W ≃ HomFamily.Compatible U₁ V W where
  toFun := HomFamily.restrict.map (V := V) (W := W) e.hom
  invFun := HomFamily.restrict.map (V := V) (W := W) e.inv
  left_inv := HomFamily.restrict.left_inv e
  right_inv := HomFamily.restrict.right_inv e

/-- The forward map of `restrictEquiv` is restriction along the forward index map. -/
@[simp, stacks 0B15 "index-isomorphism family equivalence forward map"]
theorem HomFamily.restrictEquiv.apply {U₁ U₂ : D ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : Dᵒᵖ ⥤ C) (F : HomFamily.Compatible U₂ V W) :
    HomFamily.restrictEquiv e V W F =
      HomFamily.restrict.map (V := V) (W := W) e.hom F := sorry

/-- The inverse map of `restrictEquiv` is restriction along the inverse index map. -/
@[simp, stacks 0B15 "index-isomorphism family equivalence inverse map"]
theorem HomFamily.restrictEquiv.symm_apply {U₁ U₂ : D ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : Dᵒᵖ ⥤ C) (F : HomFamily.Compatible U₁ V W) :
    (HomFamily.restrictEquiv e V W).symm F =
      HomFamily.restrict.map (V := V) (W := W) e.inv F := sorry

/-- Evaluate index-isomorphism restriction at one degree and one index. -/
@[simp, stacks 0B15 "index-isomorphism family equivalence component"]
theorem HomFamily.restrictEquiv.apply_apply {U₁ U₂ : D ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : Dᵒᵖ ⥤ C) (F : HomFamily.Compatible U₂ V W)
    (Delta : Dᵒᵖ) (u : U₁.obj (unop Delta)) :
    (HomFamily.restrictEquiv e V W F).1 Delta u =
      F.1 Delta (e.hom.app (unop Delta) u) := sorry

/-- Evaluate inverse index-isomorphism restriction at one degree and one index. -/
@[simp, stacks 0B15 "inverse index-isomorphism family equivalence component"]
theorem HomFamily.restrictEquiv.symm_apply_apply {U₁ U₂ : D ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : Dᵒᵖ ⥤ C) (F : HomFamily.Compatible U₁ V W)
    (Delta : Dᵒᵖ) (u : U₂.obj (unop Delta)) :
    ((HomFamily.restrictEquiv e V W).symm F).1 Delta u =
      F.1 Delta (e.inv.app (unop Delta) u) := sorry

end IndexVariable

section Variance

/-- Source precomposition commutes with target postcomposition on compatible families. -/
@[simp, stacks 0B15 "source-target interchange for indexed-product families"]
theorem HomFamily.precompose.postcompose
    {U : D ⥤ Type w} {V₁ V₂ W₁ W₂ : Dᵒᵖ ⥤ C}
    (f : V₁ ⟶ V₂) (g : W₁ ⟶ W₂) :
    HomFamily.precompose.map (U := U) (W := W₁) f ≫
        HomFamily.postcompose.map (U := U) (V := V₁) g =
      HomFamily.postcompose.map (U := U) (V := V₂) g ≫
        HomFamily.precompose.map (U := U) (W := W₂) f := sorry

/-- Index restriction commutes with target postcomposition on compatible families. -/
@[simp, stacks 0B15 "index-target interchange for indexed-product families"]
theorem HomFamily.restrict.postcompose
    {U₁ U₂ : D ⥤ Type w} {V W₁ W₂ : Dᵒᵖ ⥤ C}
    (a : U₁ ⟶ U₂) (g : W₁ ⟶ W₂) :
    HomFamily.restrict.map (V := V) (W := W₁) a ≫
        HomFamily.postcompose.map (U := U₁) (V := V) g =
      HomFamily.postcompose.map (U := U₂) (V := V) g ≫
        HomFamily.restrict.map (V := V) (W := W₂) a := sorry

/-- Index restriction commutes with source precomposition on compatible families. -/
@[simp, stacks 0B15 "index-source interchange for indexed-product families"]
theorem HomFamily.restrict.precompose
    {U₁ U₂ : D ⥤ Type w} {V₁ V₂ W : Dᵒᵖ ⥤ C}
    (a : U₁ ⟶ U₂) (f : V₁ ⟶ V₂) :
    HomFamily.restrict.map (V := V₂) (W := W) a ≫
        HomFamily.precompose.map (U := U₁) (W := W) f =
      HomFamily.precompose.map (U := U₂) (W := W) f ≫
        HomFamily.restrict.map (V := V₁) (W := W) a := sorry

end Variance

section UniversalProperty

/-- Extract the indexed degreewise family determined by a morphism into an indexed product. -/
@[stacks 0B15 "extract a family from an indexed-product morphism"]
def HomFamily.ofHom {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    [HasIndexedProd U W] (f : V ⟶ indexedProd U W) :
    HomFamily U V W :=
  fun Delta u ↦ f.app Delta ≫ Pi.π (fun _ : U.obj (unop Delta) ↦ W.obj Delta) u

/-- Compute a component of the family extracted from an indexed-product map. -/
@[simp, stacks 0B15 "extracted indexed-product family component"]
theorem HomFamily.ofHom.apply {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    [HasIndexedProd U W] (f : V ⟶ indexedProd U W)
    (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    HomFamily.ofHom f Delta u =
      f.app Delta ≫ Pi.π (fun _ : U.obj (unop Delta) ↦ W.obj Delta) u := sorry

/-- The family extracted from a morphism into an indexed product is compatible. -/
@[stacks 0B15 "extracted indexed-product family compatibility"]
theorem HomFamily.ofHom.isCompatible {U : D ⥤ Type w}
    {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (f : V ⟶ indexedProd U W) :
    (HomFamily.ofHom f).IsCompatible := sorry

/-- Package the family extracted from an indexed-product morphism with its compatibility. -/
@[stacks 0B15 "compatible family extracted from an indexed-product morphism"]
def HomFamily.ofHom.compatible {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    [HasIndexedProd U W] (f : V ⟶ indexedProd U W) :
    HomFamily.Compatible U V W :=
  ⟨HomFamily.ofHom f, HomFamily.ofHom.isCompatible f⟩

/-- Compute a component of the compatible family attached to an indexed-product map. -/
@[simp, stacks 0B15 "compatible extracted indexed-product family component"]
theorem HomFamily.ofHom.compatible.apply
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (f : V ⟶ indexedProd U W) (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    (HomFamily.ofHom.compatible f).1 Delta u =
      f.app Delta ≫ Pi.π (fun _ : U.obj (unop Delta) ↦ W.obj Delta) u := sorry

/-- The product lifts associated to a compatible family satisfy the presheaf naturality square. -/
@[stacks 0B15 "assembled indexed-product family naturality"]
theorem HomFamily.toHom.commSq
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (F : HomFamily.Compatible U V W) {Delta Delta' : Dᵒᵖ}
    (f : Delta ⟶ Delta') :
    CommSq (V.map f) (Pi.lift (fun u ↦ F.1 Delta u))
      (Pi.lift (fun u ↦ F.1 Delta' u)) ((indexedProd U W).map f) := sorry

/-- Assemble a compatible degreewise family into a morphism into the indexed product. -/
@[stacks 0B15 "assemble a compatible indexed-product family"]
def HomFamily.toHom {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    [HasIndexedProd U W] (F : HomFamily.Compatible U V W) :
    V ⟶ indexedProd U W where
  app Delta := Pi.lift (fun u ↦ F.1 Delta u)
  naturality := fun {_ _} f ↦ (HomFamily.toHom.commSq F f).w

/-- Compute the degreewise component of the map assembled from a compatible family. -/
@[simp, stacks 0B15 "assembled indexed-product family component"]
theorem HomFamily.toHom.app
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (F : HomFamily.Compatible U V W) (Delta : Dᵒᵖ) :
    (HomFamily.toHom F).app Delta = Pi.lift (fun u ↦ F.1 Delta u) := sorry

/-- Projecting an assembled indexed-product map recovers the chosen family component. -/
@[reassoc (attr := simp), stacks 0B15 "assembled indexed-product family projection"]
theorem HomFamily.toHom.app_π
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (F : HomFamily.Compatible U V W) (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    (HomFamily.toHom F).app Delta ≫
        Pi.π (fun _ : U.obj (unop Delta) ↦ W.obj Delta) u =
      F.1 Delta u := sorry

/-- Assembling the family extracted from an indexed-product map recovers that map. -/
@[stacks 0B15 "indexed-product Hom-family assembly left inverse"]
theorem HomFamily.toHom.left_inv
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (f : V ⟶ indexedProd U W) :
    HomFamily.toHom (HomFamily.ofHom.compatible f) = f := sorry

/-- Extracting the family from its assembled map recovers the compatible family. -/
@[stacks 0B15 "indexed-product Hom-family assembly right inverse"]
theorem HomFamily.toHom.right_inv
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (F : HomFamily.Compatible U V W) :
    HomFamily.ofHom.compatible (HomFamily.toHom F) = F := sorry

/-- Morphisms into an indexed product are equivalent to compatible indexed families. -/
@[stacks 0B15 "indexed-product Hom-family equivalence"]
def HomFamily.homEquiv (U : D ⥤ Type w) (V W : Dᵒᵖ ⥤ C)
    [HasIndexedProd U W] :
    (V ⟶ indexedProd U W) ≃ HomFamily.Compatible U V W where
  toFun := HomFamily.ofHom.compatible
  invFun := HomFamily.toHom
  left_inv := HomFamily.toHom.left_inv
  right_inv := HomFamily.toHom.right_inv

/-- The forward map of `HomFamily.homEquiv` extracts the compatible family. -/
@[simp, stacks 0B15 "indexed-product Hom-family equivalence forward formula"]
theorem HomFamily.homEquiv.apply
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (f : V ⟶ indexedProd U W) :
    HomFamily.homEquiv U V W f = HomFamily.ofHom.compatible f := sorry

/-- The inverse map of `HomFamily.homEquiv` assembles the compatible family. -/
@[simp, stacks 0B15 "indexed-product Hom-family equivalence inverse formula"]
theorem HomFamily.homEquiv.symm_apply
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (F : HomFamily.Compatible U V W) :
    (HomFamily.homEquiv U V W).symm F = HomFamily.toHom F := sorry

/-- The indexed-product Hom-family equivalence is natural under source precomposition. -/
@[stacks 0B15 "indexed-product Hom-family source naturality"]
theorem HomFamily.homEquiv.precompose
    {U : D ⥤ Type w} {V₁ V₂ W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (f : V₁ ⟶ V₂) (h : V₂ ⟶ indexedProd U W) :
    HomFamily.ofHom.compatible (f ≫ h) =
      HomFamily.precompose.map (U := U) (W := W) f
        (HomFamily.ofHom.compatible h) := sorry

/-- The indexed-product Hom-family equivalence is natural under target postcomposition. -/
@[stacks 0B15 "indexed-product Hom-family target naturality"]
theorem HomFamily.homEquiv.postcompose
    {U : D ⥤ Type w} {V W₁ W₂ : Dᵒᵖ ⥤ C}
    [HasIndexedProd U W₁] [HasIndexedProd U W₂]
    (g : W₁ ⟶ W₂) (h : V ⟶ indexedProd U W₁) :
    HomFamily.ofHom.compatible (h ≫ indexedProd.hom U g) =
      HomFamily.postcompose.map (U := U) (V := V) g
        (HomFamily.ofHom.compatible h) := sorry

/-- The indexed-product Hom-family equivalence is natural under index restriction. -/
@[stacks 0B15 "indexed-product Hom-family index naturality"]
theorem HomFamily.homEquiv.restrict
    {U₁ U₂ : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C}
    [HasIndexedProd U₁ W] [HasIndexedProd U₂ W]
    (a : U₁ ⟶ U₂) (h : V ⟶ indexedProd U₂ W) :
    HomFamily.ofHom.compatible (h ≫ indexedProd.indexHom W a) =
      HomFamily.restrict.map (V := V) (W := W) a
        (HomFamily.ofHom.compatible h) := sorry

/-- Compatible degreewise families are represented by the indexed product. -/
@[stacks 0B15 "representability of compatible indexed-product families"]
noncomputable def HomFamily.representableBy
    (U : D ⥤ Type w) (W : Dᵒᵖ ⥤ C) [HasIndexedProd U W] :
    (HomFamily.functor U W).RepresentableBy (indexedProd U W) where
  homEquiv {V} := HomFamily.homEquiv U V W
  homEquiv_comp f g := HomFamily.homEquiv.precompose f g

/-- Evaluate the representing compatible family at one degree and one index. -/
@[simp, stacks 0B15 "represented indexed-product family component"]
theorem HomFamily.representableBy.homEquiv.apply
    {U : D ⥤ Type w} {V W : Dᵒᵖ ⥤ C} [HasIndexedProd U W]
    (f : V ⟶ indexedProd U W) (Delta : Dᵒᵖ) (u : U.obj (unop Delta)) :
    ((HomFamily.representableBy (U := U) (W := W)).homEquiv f).1 Delta u =
      f.app Delta ≫ Pi.π (fun _ : U.obj (unop Delta) ↦ W.obj Delta) u := sorry

end UniversalProperty

end indexedProd

end CategoryTheory.Functor
