/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Reassociation along the left projection of a categorical pullback

Explicit forward and inverse functors for `K ⊡ (π₁ F G) ≌ (K ⋙ F) ⊡ G`, together with
their projection comparison isomorphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe vA' vA vB vD
universe uA' uA uB uD

namespace Limits.CategoricalPullback

variable {A₀' : Type uA'} [Category.{vA'} A₀']
variable {A₀ : Type uA} [Category.{vA} A₀]
variable {B₀ : Type uB} [Category.{vB} B₀]
variable {D₀ : Type uD} [Category.{vD} D₀]

namespace LeftProjection

/- `CategoricalPullback.functorEquiv` classifies one cospan cone and
`CatCospanTransform.associator` reassociates cospan transformations; neither has these two nested
pullback models as endpoints. This explicit normalization is therefore the reusable owner. -/

section Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace forward.Implementation

/-- Compatibility of the explicit forward reassociation map with the two structural
isomorphisms. -/
private theorem map_comm
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : K ⊡ (π₁ F G)} (φ : x ⟶ y) :
    (K ⋙ F).map φ.fst ≫ (F.mapIso y.iso ≪≫ y.snd.iso).hom =
      (F.mapIso x.iso ≪≫ x.snd.iso).hom ≫ G.map φ.snd.snd := sorry

end forward.Implementation

/-- The explicit forward reassociation
`A₀' ×[A₀] (A₀ ×[D₀] B₀) ⟶ A₀' ×[D₀] B₀`. -/
def forward
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    K ⊡ (π₁ F G) ⥤ (K ⋙ F) ⊡ G where
  obj x :=
    { fst := x.fst
      snd := x.snd.snd
      iso := F.mapIso x.iso ≪≫ x.snd.iso }
  map {x y} φ :=
    { fst := φ.fst
      snd := φ.snd.snd
      w := forward.Implementation.map_comm K F G φ }

namespace forward

namespace Implementation

/-- Naturality of the identity comparison on the left endpoint of `forward`. -/
private theorem fst_naturality
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : K ⊡ (π₁ F G)} (φ : x ⟶ y) :
    (forward K F G ⋙ π₁ (K ⋙ F) G).map φ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (π₁ K (π₁ F G)).map φ := sorry

/-- Naturality of the identity comparison on the right endpoint of `forward`. -/
private theorem snd_naturality
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : K ⊡ (π₁ F G)} (φ : x ⟶ y) :
    (forward K F G ⋙ π₂ (K ⋙ F) G).map φ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (π₂ K (π₁ F G) ⋙ π₂ F G).map φ := sorry

end Implementation

/-- The forward reassociation commutes with the left pullback projection. -/
def fstIso
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    forward K F G ⋙ π₁ (K ⋙ F) G ≅ π₁ K (π₁ F G) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (Implementation.fst_naturality K F G)

/-- The forward reassociation commutes with the right pullback projection. -/
def sndIso
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    forward K F G ⋙ π₂ (K ⋙ F) G ≅
      π₂ K (π₁ F G) ⋙ π₂ F G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (Implementation.snd_naturality K F G)

end forward

namespace inverse.Implementation

/-- Compatibility of the explicit inverse reassociation map with its outer identity structural
isomorphisms. -/
private theorem map_comm
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : (K ⋙ F) ⊡ G} (φ : x ⟶ y) :
    K.map φ.fst ≫ (Iso.refl (K.obj y.fst)).hom =
      (Iso.refl (K.obj x.fst)).hom ≫ K.map φ.fst := sorry

end inverse.Implementation

/-- The explicit inverse reassociation
`A₀' ×[D₀] B₀ ⟶ A₀' ×[A₀] (A₀ ×[D₀] B₀)`. -/
def inverse
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (K ⋙ F) ⊡ G ⥤ K ⊡ (π₁ F G) where
  obj x :=
    { fst := x.fst
      snd :=
        { fst := K.obj x.fst
          snd := x.snd
          iso := x.iso }
      iso := Iso.refl _ }
  map {x y} φ :=
    { fst := φ.fst
      snd :=
        { fst := K.map φ.fst
          snd := φ.snd
          w := φ.w }
      w := inverse.Implementation.map_comm K F G φ }

namespace inverse

namespace Implementation

/-- Naturality of the identity comparison on the left endpoint of `inverse`. -/
private theorem fst_naturality
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : (K ⋙ F) ⊡ G} (φ : x ⟶ y) :
    (inverse K F G ⋙ π₁ K (π₁ F G)).map φ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (π₁ (K ⋙ F) G).map φ := sorry

/-- Naturality of the identity comparison on the right endpoint of `inverse`. -/
private theorem snd_naturality
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : (K ⋙ F) ⊡ G} (φ : x ⟶ y) :
    (inverse K F G ⋙ (π₂ K (π₁ F G) ⋙ π₂ F G)).map φ ≫
        (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (π₂ (K ⋙ F) G).map φ := sorry

end Implementation

/-- The inverse reassociation commutes with the left pullback projection. -/
def fstIso
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    inverse K F G ⋙ π₁ K (π₁ F G) ≅ π₁ (K ⋙ F) G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (Implementation.fst_naturality K F G)

/-- The inverse reassociation commutes with the right pullback projection. -/
def sndIso
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    inverse K F G ⋙ (π₂ K (π₁ F G) ⋙ π₂ F G) ≅ π₂ (K ⋙ F) G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (Implementation.snd_naturality K F G)

end inverse

end Implementation

end LeftProjection

end Limits.CategoricalPullback

end CategoryTheory
