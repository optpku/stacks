module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom

/-!
# Schemes over `S` as sheaves on a chosen big fppf site

A scheme `Y` over `S` need not be an object of a chosen small presentation of
`(Sch/S)_fppf`. Its functor of points on that site is the sheaf of morphisms
into `Y` compatible with the structure maps to `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry Opposite TypeCat

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Morphisms from the source scheme of an object `U` of `(Sch/S)_fppf` to a
scheme `Y` over `S`. -/
def OverSchemeHom {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier} (Y : Scheme.{u})
    (hY : Y ⟶ 𝒮.toScheme.obj S) (U : 𝒮.bigSite S) : Type u :=
  { f : (𝒮.bigToScheme S).obj U ⟶ Y // f ≫ hY = 𝒮.toScheme.map U.hom }

/-- A morphism lies in `OverSchemeHom Y hY U` if and only if it is a morphism
of schemes over `S`. -/
theorem mem_overSchemeHom {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Y : Scheme.{u}} {hY : Y ⟶ 𝒮.toScheme.obj S} {U : 𝒮.bigSite S}
    (f : (𝒮.bigToScheme S).obj U ⟶ Y) :
    (∃ p : OverSchemeHom Y hY U, p.val = f) ↔
      f ≫ hY = 𝒮.toScheme.map U.hom :=
  sorry

/-- Restriction of an over-`S` morphism along a morphism of the chosen site. -/
def overSchemeHomMap {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Y : Scheme.{u}} {hY : Y ⟶ 𝒮.toScheme.obj S} {U V : 𝒮.bigSite S} (φ : V ⟶ U)
    (f : OverSchemeHom Y hY U) : OverSchemeHom Y hY V :=
  ⟨(𝒮.bigToScheme S).map φ ≫ f.val, sorry⟩

/-- `overSchemeHomMap` is composition with the image of the site morphism. -/
theorem overSchemeHomMap_val {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Y : Scheme.{u}} {hY : Y ⟶ 𝒮.toScheme.obj S} {U V : 𝒮.bigSite S} (φ : V ⟶ U)
    (f : OverSchemeHom Y hY U) :
    (overSchemeHomMap φ f).val = (𝒮.bigToScheme S).map φ ≫ f.val :=
  sorry

/-- The presheaf on `(Sch/S)_fppf` of morphisms into `Y` over `S`. -/
def overSchemePresheaf {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (Y : Scheme.{u}) (hY : Y ⟶ 𝒮.toScheme.obj S) :
    (𝒮.bigSite S)ᵒᵖ ⥤ Type (max u v) where
  obj U := ULift.{max u v} (OverSchemeHom Y hY U.unop)
  map {U V} φ := ofHom fun x ↦ ⟨overSchemeHomMap φ.unop x.down⟩
  map_id := sorry
  map_comp := sorry

/-- On objects, `overSchemePresheaf` is the universe lift of `OverSchemeHom`. -/
theorem overSchemePresheaf_obj {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (Y : Scheme.{u}) (hY : Y ⟶ 𝒮.toScheme.obj S) (U : (𝒮.bigSite S)ᵒᵖ) :
    (overSchemePresheaf Y hY).obj U =
      ULift.{max u v} (OverSchemeHom Y hY U.unop) :=
  sorry

/-- Restriction maps of `overSchemePresheaf` are `overSchemeHomMap`. -/
theorem overSchemePresheaf_map {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (Y : Scheme.{u}) (hY : Y ⟶ 𝒮.toScheme.obj S) {U V : (𝒮.bigSite S)ᵒᵖ}
    (φ : U ⟶ V) :
    (overSchemePresheaf Y hY).map φ =
      ofHom fun x ↦ ⟨overSchemeHomMap φ.unop x.down⟩ :=
  sorry

/-- The functor of points of `Y` over `S` is an fppf sheaf on the chosen site. -/
theorem overSchemePresheaf_isSheaf {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (Y : Scheme.{u}) (hY : Y ⟶ 𝒮.toScheme.obj S) :
    Presheaf.IsSheaf (𝒮.bigTopology S) (overSchemePresheaf Y hY) :=
  sorry

/-- The fppf sheaf on `(Sch/S)_fppf` represented by a scheme `Y` over `S`. -/
def overSchemeSheaf {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (Y : Scheme.{u}) (hY : Y ⟶ 𝒮.toScheme.obj S) :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  ⟨overSchemePresheaf Y hY, overSchemePresheaf_isSheaf Y hY⟩

/-- The underlying presheaf of `overSchemeSheaf` is `overSchemePresheaf`. -/
theorem overSchemeSheaf_obj {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (Y : Scheme.{u}) (hY : Y ⟶ 𝒮.toScheme.obj S) :
    (overSchemeSheaf Y hY).obj = overSchemePresheaf Y hY :=
  sorry

/-- Yoneda: maps from the sheafified representable of `U` into `overSchemeSheaf Y hY`
are morphisms of schemes `U ⟶ Y` over `S`. -/
def overSchemeSheaf.homEquiv {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] {Y : Scheme.{u}}
    {hY : Y ⟶ 𝒮.toScheme.obj S} (U : 𝒮.bigSite S) :
    ((𝒮.bigTopology S).sheafifiedRepresentable U ⟶ overSchemeSheaf Y hY) ≃
      OverSchemeHom Y hY U :=
  ((𝒮.bigTopology S).sheafifiedRepresentableHomEquiv (overSchemeSheaf Y hY) U).trans
    Equiv.ulift

/-- `overSchemeSheaf.homEquiv` evaluates as the sheafified Yoneda equivalence
followed by `ULift.down`. -/
theorem overSchemeSheaf.homEquiv_apply {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Y : Scheme.{u}} {hY : Y ⟶ 𝒮.toScheme.obj S} {U : 𝒮.bigSite S}
    (α : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ overSchemeSheaf Y hY) :
    overSchemeSheaf.homEquiv U α =
      ((𝒮.bigTopology S).sheafifiedRepresentableHomEquiv (overSchemeSheaf Y hY) U α).down :=
  sorry

/-- The scheme morphism extracted by `overSchemeSheaf.homEquiv` is a morphism over
`S`, and every such morphism arises uniquely. -/
theorem overSchemeSheaf.homEquiv_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Y : Scheme.{u}} {hY : Y ⟶ 𝒮.toScheme.obj S} {U : 𝒮.bigSite S}
    (α : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ overSchemeSheaf Y hY) :
    (overSchemeSheaf.homEquiv U α).val ≫ hY = 𝒮.toScheme.map U.hom ∧
      ∀ (f : OverSchemeHom Y hY U), overSchemeSheaf.homEquiv U α = f ↔
        (𝒮.bigTopology S).sheafifiedRepresentableHomEquiv (overSchemeSheaf Y hY) U α =
          ⟨f⟩ :=
  sorry

end AlgebraicGeometry.ChosenBigFppfSite
