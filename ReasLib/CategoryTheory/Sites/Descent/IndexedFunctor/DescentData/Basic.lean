module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Basic

import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic transport of descent data

This leaf constructs the functor on categories of descent data induced by an indexed functor
over the identity of the base category.  It contains the object and morphism constructions and
their componentwise computation rules, but not functoriality in modifications or fiberwise
properties.
-/

@[expose] public section

universe t uC vC uF vF uG vG

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable (H : IndexedFunctor (𝟭 C) F G)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The compatibility morphism of the image of a descent datum under an indexed functor over
the identity base functor. -/
@[stacks 026E "indexed-functor descent compatibility morphism"]
def mapDescentData.Object.Hom.apply (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.obj ((H.app (X i₁)).obj (D.obj i₁)) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((H.app (X i₂)).obj (D.obj i₂)) :=
  H.mapHom f₁ f₂ (D.hom q f₁ f₂ hf₁ hf₂)

/-- The mapped compatibility morphisms commute with further restriction. -/
@[stacks 026E "indexed-functor descent compatibility restriction"]
theorem mapDescentData.Object.Hom.pull (D : F.DescentData f)
    ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    (hq : g ≫ q = q') ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {hgf₁f : gf₁ ≫ f i₁ = q'} {hgf₂f : gf₂ ≫ f i₂ = q'} :
    pullHom (mapDescentData.Object.Hom.apply H f D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      mapDescentData.Object.Hom.apply H f D q' gf₁ gf₂ hgf₁f hgf₂f := sorry

/-- The mapped compatibility morphism from a restricted object to itself is the identity. -/
@[stacks 026E "indexed-functor descent compatibility identity"]
theorem mapDescentData.Object.Hom.self (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄
    (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    mapDescentData.Object.Hom.apply H f D q g g hg hg = 𝟙 _ := sorry

/-- The mapped compatibility morphisms satisfy the cocycle composition law. -/
@[stacks 026E "indexed-functor descent compatibility composition"]
theorem mapDescentData.Object.Hom.comp (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (hf₃ : f₃ ≫ f i₃ = q) :
    mapDescentData.Object.Hom.apply H f D q f₁ f₂ hf₁ hf₂ ≫
        mapDescentData.Object.Hom.apply H f D q f₂ f₃ hf₂ hf₃ =
      mapDescentData.Object.Hom.apply H f D q f₁ f₃ hf₁ hf₃ := sorry

/-- Transport a descent datum through an indexed functor over the identity base functor. -/
@[stacks 026E "indexed-functor descent object transport"]
def mapDescentData.Object.apply (H : IndexedFunctor (𝟭 C) F G)
    (D : F.DescentData f) : G.DescentData f where
  obj i := (H.app (X i)).obj (D.obj i)
  hom _ q _ _ f₁ f₂ hf₁ hf₂ :=
    mapDescentData.Object.Hom.apply H f D q f₁ f₂ hf₁ hf₂
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    mapDescentData.Object.Hom.pull H f D g q q' hq
      f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self _ q _ g hg := mapDescentData.Object.Hom.self H f D q g hg
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    mapDescentData.Object.Hom.comp H f D q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- Mapping the objects of a descent datum is computed componentwise by the indexed functor. -/
@[simp, stacks 026E "indexed-functor descent object transport computation"]
theorem mapDescentData.Object.obj (D : F.DescentData f) (i : ι) :
    (mapDescentData.Object.apply f H D).obj i =
      (H.app (X i)).obj (D.obj i) := sorry

/-- Mapping the compatibility morphisms of a descent datum is `IndexedFunctor.mapHom`. -/
@[simp, stacks 026E "indexed-functor descent compatibility computation"]
theorem mapDescentData.Object.hom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (mapDescentData.Object.apply f H D).hom q f₁ f₂ hf₁ hf₂ =
      H.mapHom f₁ f₂ (D.hom q f₁ f₂ hf₁ hf₂) := sorry

/-- Componentwise mapping of a morphism of descent data respects its compatibility squares. -/
@[stacks 026E "indexed-functor descent morphism compatibility"]
theorem mapDescentData.Map.comm
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.map ((H.app (X i₁)).map (φ.hom i₁)) ≫
        (mapDescentData.Object.apply f H D₂).hom q f₁ f₂ hf₁ hf₂ =
      (mapDescentData.Object.apply f H D₁).hom q f₁ f₂ hf₁ hf₂ ≫
        (G.map f₂.op.toLoc).toFunctor.map ((H.app (X i₂)).map (φ.hom i₂)) := sorry

/-- Transport a morphism of descent data componentwise through an indexed functor. -/
@[stacks 026E "indexed-functor descent morphism transport"]
def mapDescentData.Map.apply (H : IndexedFunctor (𝟭 C) F G)
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) :
    mapDescentData.Object.apply f H D₁ ⟶
      mapDescentData.Object.apply f H D₂ where
  hom i := (H.app (X i)).map (φ.hom i)
  comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
    mapDescentData.Map.comm H f φ q f₁ f₂ hf₁ hf₂

/-- Mapping an identity morphism of descent data gives the identity morphism. -/
@[simp, stacks 026E "indexed-functor descent morphism identity"]
theorem mapDescentData.Map.id (D : F.DescentData f) :
    mapDescentData.Map.apply f H (𝟙 D) =
      𝟙 (mapDescentData.Object.apply f H D) := sorry

/-- Mapping a composite morphism of descent data gives the composite of the mapped morphisms. -/
@[simp, stacks 026E "indexed-functor descent morphism composition"]
theorem mapDescentData.Map.comp
    {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (ψ : D₂ ⟶ D₃) :
    mapDescentData.Map.apply f H (φ ≫ ψ) =
      mapDescentData.Map.apply f H φ ≫
        mapDescentData.Map.apply f H ψ := sorry

/-- The functor on descent-data categories induced by an indexed functor over the identity
base functor. -/
@[stacks 026E "indexed-functor descent-data transport functor"]
def mapDescentData (H : IndexedFunctor (𝟭 C) F G) :
    F.DescentData f ⥤ G.DescentData f where
  obj := mapDescentData.Object.apply f H
  map := mapDescentData.Map.apply f H
  map_id := mapDescentData.Map.id H f
  map_comp := mapDescentData.Map.comp H f

/-- The object part of `mapDescentData` is `mapDescentData.Object.apply`. -/
@[simp, stacks 026E "indexed-functor descent transport object readout"]
theorem mapDescentData.obj (D : F.DescentData f) :
    (H.mapDescentData f).obj D =
      mapDescentData.Object.apply f H D := sorry

/-- The morphism part of `mapDescentData` is `mapDescentData.Map.apply`. -/
@[simp, stacks 026E "indexed-functor descent transport morphism readout"]
theorem mapDescentData.map
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) :
    (H.mapDescentData f).map φ =
      mapDescentData.Map.apply f H φ := sorry

/-- On object components, `mapDescentData` applies the corresponding fiber functor. -/
@[simp, stacks 026E "indexed-functor descent transport component object"]
theorem mapDescentData.obj_obj (D : F.DescentData f) (i : ι) :
    ((H.mapDescentData f).obj D).obj i =
      (H.app (X i)).obj (D.obj i) := sorry

/-- On compatibility morphisms, `mapDescentData` applies restricted-hom transport. -/
@[simp, stacks 026E "indexed-functor descent transport compatibility readout"]
theorem mapDescentData.obj_hom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((H.mapDescentData f).obj D).hom q f₁ f₂ hf₁ hf₂ =
      H.mapHom f₁ f₂ (D.hom q f₁ f₂ hf₁ hf₂) := sorry

/-- On morphism components, `mapDescentData` applies the corresponding fiber functor. -/
@[simp, stacks 026E "indexed-functor descent transport morphism component"]
theorem mapDescentData.map_hom
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) (i : ι) :
    ((H.mapDescentData f).map φ).hom i =
      (H.app (X i)).map (φ.hom i) := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
