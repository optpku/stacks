/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedCoproduct
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017B

# Compatible families for indexed coproducts

For an indexing diagram `U : J ⥤ Type w` and `C`-valued diagrams `V` and `W`, this
module packages the compatible degreewise families of maps from `V` to `W` indexed by `U`.
When `indexedCoprod U V` exists, such families are corepresented by the indexed coproduct.

This is the category-generic universal-property owner underlying simplicial copowers.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w i d v u

namespace CategoryTheory.Functor

variable {J : Type i} [Category.{d} J] {C : Type u} [Category.{v} C]

namespace indexedCoprod

section Families

variable (U : J ⥤ Type w) (V W : J ⥤ C)

/-- A degreewise family of morphisms from `V` to `W`, indexed by the elements of `U`. -/
@[stacks 017B "indexed-coproduct Hom families"]
abbrev HomFamily :=
  ∀ Delta : J, U.obj Delta → (V.obj Delta ⟶ W.obj Delta)

namespace HomFamily

/-- Compatibility of an indexed degreewise Hom family with the diagram structure maps. -/
@[stacks 017B "compatibility of indexed-coproduct morphism families"]
def IsCompatible {U : J ⥤ Type w} {V W : J ⥤ C}
    (F : HomFamily U V W) : Prop :=
  ∀ ⦃Delta Delta' : J⦄ (f : Delta ⟶ Delta') (u : U.obj Delta),
    V.map f ≫ F Delta' (U.map f u) = F Delta u ≫ W.map f

/-- A family is compatible precisely when it satisfies the displayed naturality equations. -/
@[stacks 017B "indexed-coproduct compatibility equations"]
theorem isCompatible_iff {U : J ⥤ Type w} {V W : J ⥤ C}
    (F : HomFamily U V W) :
    F.IsCompatible ↔
      ∀ ⦃Delta Delta' : J⦄ (f : Delta ⟶ Delta') (u : U.obj Delta),
        V.map f ≫ F Delta' (U.map f u) = F Delta u ≫ W.map f := sorry

/-- Compatible degreewise families of morphisms indexed by `U`. -/
@[stacks 017B "compatible indexed-coproduct morphism families"]
abbrev Compatible :=
  { F : HomFamily U V W // F.IsCompatible }

end HomFamily

end Families

section TargetVariable

/-- Postcompose every component of a compatible family with a morphism of target diagrams. -/
@[stacks 017D "postcomposition of compatible indexed-coproduct families"]
def HomFamily.postcompose {U : J ⥤ Type w} {V W W' : J ⥤ C}
    (g : W ⟶ W') (F : HomFamily.Compatible U V W) :
    HomFamily U V W' :=
  fun Delta u ↦ F.1 Delta u ≫ g.app Delta

/-- Evaluate target postcomposition at one degree and one index. -/
@[simp, stacks 017D "target postcomposition component"]
theorem HomFamily.postcompose.apply {U : J ⥤ Type w}
    {V W W' : J ⥤ C} (g : W ⟶ W')
    (F : HomFamily.Compatible U V W) (Delta : J) (u : U.obj Delta) :
    HomFamily.postcompose g F Delta u = F.1 Delta u ≫ g.app Delta := sorry

/-- Postcomposition preserves compatibility of indexed degreewise families. -/
@[stacks 017D "postcomposition preserves indexed-coproduct compatibility"]
theorem HomFamily.postcompose.isCompatible {U : J ⥤ Type w}
    {V W W' : J ⥤ C} (g : W ⟶ W')
    (F : HomFamily.Compatible U V W) :
    (HomFamily.postcompose g F).IsCompatible := sorry

/-- Postcomposition as a morphism between the corresponding types of compatible families. -/
@[stacks 017D "map on compatible indexed-coproduct families"]
def HomFamily.postcompose.map {U : J ⥤ Type w} {V W W' : J ⥤ C}
    (g : W ⟶ W') :
    HomFamily.Compatible U V W ⟶ HomFamily.Compatible U V W' :=
  TypeCat.ofHom fun F =>
    ⟨HomFamily.postcompose g F, HomFamily.postcompose.isCompatible g F⟩

/-- Evaluate the bundled target-postcomposition map at one degree and one index. -/
@[simp, stacks 017D "bundled target postcomposition component"]
theorem HomFamily.postcompose.map.apply {U : J ⥤ Type w}
    {V W W' : J ⥤ C} (g : W ⟶ W')
    (F : HomFamily.Compatible U V W) (Delta : J) (u : U.obj Delta) :
    (HomFamily.postcompose.map g F).1 Delta u =
      F.1 Delta u ≫ g.app Delta := sorry

/-- Postcomposition by an identity induces the identity map on compatible families. -/
@[simp, stacks 017D "identity postcomposition on indexed-coproduct families"]
theorem HomFamily.postcompose.map_id (U : J ⥤ Type w)
    (V W : J ⥤ C) :
    HomFamily.postcompose.map (U := U) (V := V) (𝟙 W) =
      𝟙 (HomFamily.Compatible U V W) := sorry

/-- Postcomposition of compatible families respects composition of target morphisms. -/
@[simp, stacks 017D "composition of postcomposition maps on indexed-coproduct families"]
theorem HomFamily.postcompose.map_comp (U : J ⥤ Type w) (V : J ⥤ C)
    {W₁ W₂ W₃ : J ⥤ C} (g : W₁ ⟶ W₂) (h : W₂ ⟶ W₃) :
    HomFamily.postcompose.map (U := U) (V := V) (g ≫ h) =
      HomFamily.postcompose.map (U := U) (V := V) g ≫
        HomFamily.postcompose.map (U := U) (V := V) h := sorry

/-- Compatible families as a functor of the target diagram. -/
@[stacks 017D "compatible indexed-coproduct Hom-family functor"]
def HomFamily.functor (U : J ⥤ Type w) (V : J ⥤ C) :
    (J ⥤ C) ⥤ Type (max i w v) where
  obj W := HomFamily.Compatible U V W
  map g := HomFamily.postcompose.map (U := U) (V := V) g
  map_id W := HomFamily.postcompose.map_id U V W
  map_comp g h := HomFamily.postcompose.map_comp U V g h

end TargetVariable

section SourceVariable

/-- Precompose every component of a compatible family with a morphism of source diagrams. -/
@[stacks 017D "precomposition of compatible indexed-coproduct families"]
def HomFamily.precompose {U : J ⥤ Type w} {V₁ V₂ W : J ⥤ C}
    (f : V₁ ⟶ V₂) (F : HomFamily.Compatible U V₂ W) :
    HomFamily U V₁ W :=
  fun Delta u ↦ f.app Delta ≫ F.1 Delta u

/-- Evaluate source precomposition at one degree and one index. -/
@[simp, stacks 017D "source precomposition component"]
theorem HomFamily.precompose.apply {U : J ⥤ Type w}
    {V₁ V₂ W : J ⥤ C} (f : V₁ ⟶ V₂)
    (F : HomFamily.Compatible U V₂ W) (Delta : J) (u : U.obj Delta) :
    HomFamily.precompose f F Delta u = f.app Delta ≫ F.1 Delta u := sorry

/-- Precomposition preserves compatibility of indexed degreewise families. -/
@[stacks 017D "precomposition preserves indexed-coproduct compatibility"]
theorem HomFamily.precompose.isCompatible {U : J ⥤ Type w}
    {V₁ V₂ W : J ⥤ C} (f : V₁ ⟶ V₂)
    (F : HomFamily.Compatible U V₂ W) :
    (HomFamily.precompose f F).IsCompatible := sorry

/-- Precomposition as a morphism between the corresponding types of compatible families. -/
@[stacks 017D "precomposition map on compatible indexed-coproduct families"]
def HomFamily.precompose.map {U : J ⥤ Type w} {V₁ V₂ W : J ⥤ C}
    (f : V₁ ⟶ V₂) :
    HomFamily.Compatible U V₂ W ⟶ HomFamily.Compatible U V₁ W :=
  TypeCat.ofHom fun F =>
    ⟨HomFamily.precompose f F, HomFamily.precompose.isCompatible f F⟩

/-- Evaluate the bundled source-precomposition map at one degree and one index. -/
@[simp, stacks 017D "bundled source precomposition component"]
theorem HomFamily.precompose.map.apply {U : J ⥤ Type w}
    {V₁ V₂ W : J ⥤ C} (f : V₁ ⟶ V₂)
    (F : HomFamily.Compatible U V₂ W) (Delta : J) (u : U.obj Delta) :
    (HomFamily.precompose.map f F).1 Delta u =
      f.app Delta ≫ F.1 Delta u := sorry

/-- Precomposition by an identity induces the identity map on compatible families. -/
@[simp, stacks 017D "identity precomposition on indexed-coproduct families"]
theorem HomFamily.precompose.map_id (U : J ⥤ Type w)
    (V W : J ⥤ C) :
    HomFamily.precompose.map (U := U) (W := W) (𝟙 V) =
      𝟙 (HomFamily.Compatible U V W) := sorry

/-- Precomposition reverses composition of source morphisms. -/
@[simp, stacks 017D "composition of precomposition maps on indexed-coproduct families"]
theorem HomFamily.precompose.map_comp (U : J ⥤ Type w) (W : J ⥤ C)
    {V₁ V₂ V₃ : J ⥤ C} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) :
    HomFamily.precompose.map (U := U) (W := W) (f ≫ g) =
      HomFamily.precompose.map (U := U) (W := W) g ≫
        HomFamily.precompose.map (U := U) (W := W) f := sorry

end SourceVariable

section IndexVariable

/-- Restrict a compatible family along a morphism of indexing diagrams. -/
@[stacks 017D "restriction of compatible indexed-coproduct families"]
def HomFamily.restrict {U₁ U₂ : J ⥤ Type w} {V W : J ⥤ C}
    (a : U₁ ⟶ U₂) (F : HomFamily.Compatible U₂ V W) :
    HomFamily U₁ V W :=
  fun Delta u ↦ F.1 Delta (a.app Delta u)

/-- Evaluate index restriction at one degree and one index. -/
@[simp, stacks 017D "index restriction component"]
theorem HomFamily.restrict.apply {U₁ U₂ : J ⥤ Type w}
    {V W : J ⥤ C} (a : U₁ ⟶ U₂)
    (F : HomFamily.Compatible U₂ V W) (Delta : J) (u : U₁.obj Delta) :
    HomFamily.restrict a F Delta u = F.1 Delta (a.app Delta u) := sorry

/-- Restriction preserves compatibility of indexed degreewise families. -/
@[stacks 017D "restriction preserves indexed-coproduct compatibility"]
theorem HomFamily.restrict.isCompatible {U₁ U₂ : J ⥤ Type w}
    {V W : J ⥤ C} (a : U₁ ⟶ U₂)
    (F : HomFamily.Compatible U₂ V W) :
    (HomFamily.restrict a F).IsCompatible := sorry

/-- Restriction as a morphism between the corresponding types of compatible families. -/
@[stacks 017D "restriction map on compatible indexed-coproduct families"]
def HomFamily.restrict.map {U₁ U₂ : J ⥤ Type w} {V W : J ⥤ C}
    (a : U₁ ⟶ U₂) :
    HomFamily.Compatible U₂ V W ⟶ HomFamily.Compatible U₁ V W :=
  TypeCat.ofHom fun F =>
    ⟨HomFamily.restrict a F, HomFamily.restrict.isCompatible a F⟩

/-- Evaluate the bundled index-restriction map at one degree and one index. -/
@[simp, stacks 017D "bundled index restriction component"]
theorem HomFamily.restrict.map.apply {U₁ U₂ : J ⥤ Type w}
    {V W : J ⥤ C} (a : U₁ ⟶ U₂)
    (F : HomFamily.Compatible U₂ V W) (Delta : J) (u : U₁.obj Delta) :
    (HomFamily.restrict.map a F).1 Delta u =
      F.1 Delta (a.app Delta u) := sorry

/-- Restriction along an identity induces the identity map on compatible families. -/
@[simp, stacks 017D "identity restriction on indexed-coproduct families"]
theorem HomFamily.restrict.map_id (U : J ⥤ Type w)
    (V W : J ⥤ C) :
    HomFamily.restrict.map (V := V) (W := W) (𝟙 U) =
      𝟙 (HomFamily.Compatible U V W) := sorry

/-- Restriction reverses composition of indexing-diagram morphisms. -/
@[simp, stacks 017D "composition of restriction maps on indexed-coproduct families"]
theorem HomFamily.restrict.map_comp (V W : J ⥤ C)
    {U₁ U₂ U₃ : J ⥤ Type w} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) :
    HomFamily.restrict.map (V := V) (W := W) (a ≫ b) =
      HomFamily.restrict.map (V := V) (W := W) b ≫
        HomFamily.restrict.map (V := V) (W := W) a := sorry

/-- Restriction along the inverse of an index isomorphism undoes restriction along its
forward map. -/
@[stacks 017D "index-isomorphism restriction left inverse"]
theorem HomFamily.restrict.left_inv {U₁ U₂ : J ⥤ Type w} {V W : J ⥤ C}
    (e : U₁ ≅ U₂) (F : HomFamily.Compatible U₂ V W) :
    HomFamily.restrict.map (V := V) (W := W) e.inv
        (HomFamily.restrict.map (V := V) (W := W) e.hom F) =
      F := sorry

/-- Restriction along an index isomorphism undoes restriction along its inverse. -/
@[stacks 017D "index-isomorphism restriction right inverse"]
theorem HomFamily.restrict.right_inv {U₁ U₂ : J ⥤ Type w} {V W : J ⥤ C}
    (e : U₁ ≅ U₂) (F : HomFamily.Compatible U₁ V W) :
    HomFamily.restrict.map (V := V) (W := W) e.hom
        (HomFamily.restrict.map (V := V) (W := W) e.inv F) =
      F := sorry

/-- An isomorphism of indexing diagrams induces an equivalence of compatible families, in
the contravariant direction of index restriction. -/
@[stacks 017D "compatible-family equivalence under index isomorphism"]
def HomFamily.restrictEquiv {U₁ U₂ : J ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : J ⥤ C) :
    HomFamily.Compatible U₂ V W ≃ HomFamily.Compatible U₁ V W where
  toFun := HomFamily.restrict.map (V := V) (W := W) e.hom
  invFun := HomFamily.restrict.map (V := V) (W := W) e.inv
  left_inv := HomFamily.restrict.left_inv e
  right_inv := HomFamily.restrict.right_inv e

/-- The forward map of `restrictEquiv` is restriction along the forward index map. -/
@[simp, stacks 017D "index-isomorphism family equivalence forward map"]
theorem HomFamily.restrictEquiv.apply {U₁ U₂ : J ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : J ⥤ C) (F : HomFamily.Compatible U₂ V W) :
    HomFamily.restrictEquiv e V W F =
      HomFamily.restrict.map (V := V) (W := W) e.hom F := sorry

/-- The inverse map of `restrictEquiv` is restriction along the inverse index map. -/
@[simp, stacks 017D "index-isomorphism family equivalence inverse map"]
theorem HomFamily.restrictEquiv.symm_apply {U₁ U₂ : J ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : J ⥤ C) (F : HomFamily.Compatible U₁ V W) :
    (HomFamily.restrictEquiv e V W).symm F =
      HomFamily.restrict.map (V := V) (W := W) e.inv F := sorry

/-- Evaluate index-isomorphism restriction at one degree and one index. -/
@[simp, stacks 017D "index-isomorphism family equivalence component"]
theorem HomFamily.restrictEquiv.apply_apply {U₁ U₂ : J ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : J ⥤ C) (F : HomFamily.Compatible U₂ V W)
    (Delta : J) (u : U₁.obj Delta) :
    (HomFamily.restrictEquiv e V W F).1 Delta u =
      F.1 Delta (e.hom.app Delta u) := sorry

/-- Evaluate inverse index-isomorphism restriction at one degree and one index. -/
@[simp, stacks 017D "inverse index-isomorphism family equivalence component"]
theorem HomFamily.restrictEquiv.symm_apply_apply {U₁ U₂ : J ⥤ Type w}
    (e : U₁ ≅ U₂) (V W : J ⥤ C) (F : HomFamily.Compatible U₁ V W)
    (Delta : J) (u : U₂.obj Delta) :
    ((HomFamily.restrictEquiv e V W).symm F).1 Delta u =
      F.1 Delta (e.inv.app Delta u) := sorry

end IndexVariable

section Variance

/-- Source precomposition commutes with target postcomposition on compatible families. -/
@[simp, stacks 017D "source-target interchange for indexed-coproduct families"]
theorem HomFamily.precompose.postcompose
    {U : J ⥤ Type w} {V₁ V₂ W₁ W₂ : J ⥤ C}
    (f : V₁ ⟶ V₂) (g : W₁ ⟶ W₂) :
    HomFamily.precompose.map (U := U) (W := W₁) f ≫
        HomFamily.postcompose.map (U := U) (V := V₁) g =
      HomFamily.postcompose.map (U := U) (V := V₂) g ≫
        HomFamily.precompose.map (U := U) (W := W₂) f := sorry

/-- Index restriction commutes with target postcomposition on compatible families. -/
@[simp, stacks 017D "index-target interchange for indexed-coproduct families"]
theorem HomFamily.restrict.postcompose
    {U₁ U₂ : J ⥤ Type w} {V W₁ W₂ : J ⥤ C}
    (a : U₁ ⟶ U₂) (g : W₁ ⟶ W₂) :
    HomFamily.restrict.map (V := V) (W := W₁) a ≫
        HomFamily.postcompose.map (U := U₁) (V := V) g =
      HomFamily.postcompose.map (U := U₂) (V := V) g ≫
        HomFamily.restrict.map (V := V) (W := W₂) a := sorry

/-- Index restriction commutes with source precomposition on compatible families. -/
@[simp, stacks 017D "index-source interchange for indexed-coproduct families"]
theorem HomFamily.restrict.precompose
    {U₁ U₂ : J ⥤ Type w} {V₁ V₂ W : J ⥤ C}
    (a : U₁ ⟶ U₂) (f : V₁ ⟶ V₂) :
    HomFamily.restrict.map (V := V₂) (W := W) a ≫
        HomFamily.precompose.map (U := U₁) (W := W) f =
      HomFamily.precompose.map (U := U₂) (W := W) f ≫
        HomFamily.restrict.map (V := V₁) (W := W) a := sorry

end Variance

section UniversalProperty

/-- Extract the indexed degreewise family determined by a morphism from an indexed coproduct. -/
@[stacks 017D "extract a family from an indexed-coproduct morphism"]
def HomFamily.ofHom {U : J ⥤ Type w} {V W : J ⥤ C}
    [HasIndexedCoprod U V] (f : indexedCoprod U V ⟶ W) :
    HomFamily U V W :=
  fun Delta u ↦ Sigma.ι (fun _ : U.obj Delta ↦ V.obj Delta) u ≫ f.app Delta

/-- Compute a component of the degreewise family extracted from an indexed-coproduct map. -/
@[simp, stacks 017D "extracted indexed-coproduct family component"]
theorem HomFamily.ofHom.apply {U : J ⥤ Type w} {V W : J ⥤ C}
    [HasIndexedCoprod U V] (f : indexedCoprod U V ⟶ W)
    (Delta : J) (u : U.obj Delta) :
    HomFamily.ofHom f Delta u =
      Sigma.ι (fun _ : U.obj Delta ↦ V.obj Delta) u ≫ f.app Delta := sorry

/-- The family extracted from a morphism out of an indexed coproduct is compatible. -/
@[stacks 017D "extracted indexed-coproduct family compatibility"]
theorem HomFamily.ofHom.isCompatible {U : J ⥤ Type w}
    {V W : J ⥤ C} [HasIndexedCoprod U V]
    (f : indexedCoprod U V ⟶ W) :
    (HomFamily.ofHom f).IsCompatible := sorry

/-- Package the family extracted from an indexed-coproduct morphism with its compatibility. -/
@[stacks 017D "compatible family extracted from an indexed-coproduct morphism"]
def HomFamily.ofHom.compatible {U : J ⥤ Type w} {V W : J ⥤ C}
    [HasIndexedCoprod U V] (f : indexedCoprod U V ⟶ W) :
    HomFamily.Compatible U V W :=
  ⟨HomFamily.ofHom f, HomFamily.ofHom.isCompatible f⟩

/-- Compute a component of the compatible family attached to an indexed-coproduct map. -/
@[simp, stacks 017D "compatible extracted indexed-coproduct family component"]
theorem HomFamily.ofHom.compatible.apply
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (f : indexedCoprod U V ⟶ W) (Delta : J) (u : U.obj Delta) :
    (HomFamily.ofHom.compatible f).1 Delta u =
      Sigma.ι (fun _ : U.obj Delta ↦ V.obj Delta) u ≫ f.app Delta := sorry

/-- The coproduct maps associated to a compatible family satisfy the diagram naturality
square. -/
@[stacks 017D "assembled indexed-coproduct family naturality"]
theorem HomFamily.toHom.commSq
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (F : HomFamily.Compatible U V W) {Delta Delta' : J}
    (f : Delta ⟶ Delta') :
    CommSq ((indexedCoprod U V).map f) (Limits.Sigma.desc (fun u ↦ F.1 Delta u))
      (Limits.Sigma.desc (fun u ↦ F.1 Delta' u)) (W.map f) := sorry

/-- Assemble a compatible degreewise family into a morphism from the indexed coproduct. -/
@[stacks 017D "assemble a compatible indexed-coproduct family"]
def HomFamily.toHom {U : J ⥤ Type w} {V W : J ⥤ C}
    [HasIndexedCoprod U V] (F : HomFamily.Compatible U V W) :
    indexedCoprod U V ⟶ W where
  app Delta := Limits.Sigma.desc (fun u ↦ F.1 Delta u)
  naturality := fun {_ _} f ↦ (HomFamily.toHom.commSq F f).w

/-- Compute the degreewise component of the map assembled from a compatible family. -/
@[simp, stacks 017D "assembled indexed-coproduct family component"]
theorem HomFamily.toHom.app
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (F : HomFamily.Compatible U V W) (Delta : J) :
    (HomFamily.toHom F).app Delta =
      Limits.Sigma.desc (fun u ↦ F.1 Delta u) := sorry

/-- Projecting an assembled indexed-coproduct map recovers the chosen family component. -/
@[reassoc (attr := simp), stacks 017D "assembled indexed-coproduct family injection"]
theorem HomFamily.toHom.app_ι
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (F : HomFamily.Compatible U V W) (Delta : J) (u : U.obj Delta) :
    Sigma.ι (fun _ : U.obj Delta ↦ V.obj Delta) u ≫
        (HomFamily.toHom F).app Delta =
      F.1 Delta u := sorry

/-- Assembling the family extracted from an indexed-coproduct map recovers that map. -/
@[stacks 017D "indexed-coproduct Hom-family assembly left inverse"]
theorem HomFamily.toHom.left_inv
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (f : indexedCoprod U V ⟶ W) :
    HomFamily.toHom (HomFamily.ofHom.compatible f) = f := sorry

/-- Extracting the family from its assembled map recovers the compatible family. -/
@[stacks 017D "indexed-coproduct Hom-family assembly right inverse"]
theorem HomFamily.toHom.right_inv
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (F : HomFamily.Compatible U V W) :
    HomFamily.ofHom.compatible (HomFamily.toHom F) = F := sorry

/-- Morphisms from an indexed coproduct are equivalent to compatible indexed families. -/
@[stacks 017D "indexed-coproduct Hom-family equivalence"]
def HomFamily.homEquiv (U : J ⥤ Type w) (V W : J ⥤ C)
    [HasIndexedCoprod U V] :
    (indexedCoprod U V ⟶ W) ≃ HomFamily.Compatible U V W where
  toFun := HomFamily.ofHom.compatible
  invFun := HomFamily.toHom
  left_inv := HomFamily.toHom.left_inv
  right_inv := HomFamily.toHom.right_inv

/-- The forward map of `HomFamily.homEquiv` extracts the compatible family. -/
@[simp, stacks 017D "indexed-coproduct Hom-family equivalence forward formula"]
theorem HomFamily.homEquiv.apply
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (f : indexedCoprod U V ⟶ W) :
    HomFamily.homEquiv U V W f = HomFamily.ofHom.compatible f := sorry

/-- The inverse map of `HomFamily.homEquiv` assembles the compatible family. -/
@[simp, stacks 017D "indexed-coproduct Hom-family equivalence inverse formula"]
theorem HomFamily.homEquiv.symm_apply
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (F : HomFamily.Compatible U V W) :
    (HomFamily.homEquiv U V W).symm F = HomFamily.toHom F := sorry

/-- The indexed-coproduct Hom-family equivalence is natural under target postcomposition. -/
@[stacks 017D "indexed-coproduct Hom-family target postcomposition"]
theorem HomFamily.homEquiv.postcompose
    {U : J ⥤ Type w} {V W₁ W₂ : J ⥤ C} [HasIndexedCoprod U V]
    (g : W₁ ⟶ W₂) (f : indexedCoprod U V ⟶ W₁) :
    HomFamily.ofHom.compatible (f ≫ g) =
      HomFamily.postcompose.map (U := U) (V := V) g
        (HomFamily.ofHom.compatible f) := sorry

/-- The indexed-coproduct Hom-family equivalence is natural under source precomposition. -/
@[stacks 017D "indexed-coproduct Hom-family source naturality"]
theorem HomFamily.homEquiv.precompose
    {U : J ⥤ Type w} {V₁ V₂ W : J ⥤ C}
    [HasIndexedCoprod U V₁] [HasIndexedCoprod U V₂]
    (f : V₁ ⟶ V₂) (h : indexedCoprod U V₂ ⟶ W) :
    HomFamily.ofHom.compatible (indexedCoprod.hom U f ≫ h) =
      HomFamily.precompose.map (U := U) (W := W) f
        (HomFamily.ofHom.compatible h) := sorry

/-- The indexed-coproduct Hom-family equivalence is natural under index restriction. -/
@[stacks 017D "indexed-coproduct Hom-family index naturality"]
theorem HomFamily.homEquiv.restrict
    {U₁ U₂ : J ⥤ Type w} {V W : J ⥤ C}
    [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₂ V]
    (a : U₁ ⟶ U₂) (h : indexedCoprod U₂ V ⟶ W) :
    HomFamily.ofHom.compatible (indexedCoprod.indexHom V a ≫ h) =
      HomFamily.restrict.map (V := V) (W := W) a
        (HomFamily.ofHom.compatible h) := sorry

/-- Compatible degreewise families are corepresented by the indexed coproduct. -/
@[stacks 017D "corepresentability of compatible indexed-coproduct families"]
noncomputable def HomFamily.corepresentableBy
    (U : J ⥤ Type w) (V : J ⥤ C) [HasIndexedCoprod U V] :
    (HomFamily.functor U V).CorepresentableBy (indexedCoprod U V) where
  homEquiv {W} := HomFamily.homEquiv U V W
  homEquiv_comp g f := HomFamily.homEquiv.postcompose g f

/-- Evaluate the corepresenting compatible family at one degree and one index. -/
@[simp, stacks 017D "corepresented indexed-coproduct family component"]
theorem HomFamily.corepresentableBy.homEquiv.apply
    {U : J ⥤ Type w} {V W : J ⥤ C} [HasIndexedCoprod U V]
    (f : indexedCoprod U V ⟶ W) (Delta : J) (u : U.obj Delta) :
    ((HomFamily.corepresentableBy (U := U) (V := V)).homEquiv f).1 Delta u =
      Sigma.ι (fun _ : U.obj Delta ↦ V.obj Delta) u ≫ f.app Delta := sorry

end UniversalProperty

end indexedCoprod

end CategoryTheory.Functor
