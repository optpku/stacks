/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.AmbientSquare
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Localization
public import ReasLib.CategoryTheory.Sites.Localization.Representable.BaseChange
public import ReasLib.CategoryTheory.Sites.Localization.Representable.LowerShriek
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representable comparison for localized morphisms of ringed topoi

This leaf relates the localization of a site-presented morphism at an arrow
`c : U ⟶ f.base.obj V` to localization of its inverse-image adjunction at the corresponding
map of sheafified representables.  The canonical parameter and the slice-topos ambient square
are concrete data.  Compatibility with the forgotten structure maps is exposed separately.

The representable-localization comparison is built from a canonical pullback isomorphism, so
none of the interfaces below ask callers to supply auxiliary `IsIso` witnesses. Generic
base-change conclusions remain `IsIsomorphic` until their natural isomorphisms are constructed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.RepresentableLocalization

noncomputable section

universe u v

namespace RingedSite.Localization.Representable

section StructureObject

variable (Z : RingedSite.{u, v}) (W : Z)
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{max u v})]
variable [∀ P : Functor (Over W)ᵒᵖ (Type (max u v)),
  (Over.forget W).op.HasLeftKanExtension P]

/-- The explicit representable-localization comparison identifies restriction of the forgotten
structure sheaf to `Z / W` with the slice-product structure object over `h_W^#`. -/
@[stacks 04J3 "localized structure object", stacks 04J9 "structure identification"]
theorem structureObjectComparison_isIso :
    IsIso
      ((GrothendieckTopology.RepresentableLocalization.lowerShriekOverPullbackComparison
        (J := Z.siteTopology) W).app
          (RingedSite.Hom.underlyingStructureSheaf Z)) := sorry

end StructureObject

variable {X Y : RingedSite.{u, v}}
variable (f : X.Hom Y)
variable {V : Y} {U : X} (c : U ⟶ f.base.obj V)

/-- The map `h_U^# ⟶ f⁻¹(h_V^#)` induced by `c : U ⟶ f.base.obj V`. -/
@[stacks 04J9 "representable parameter"]
noncomputable abbrev parameter :
    X.siteTopology.sheafifiedRepresentable U ⟶
      (f.base.sheafPullback (Type (max u v))
        Y.siteTopology X.siteTopology).obj
        (Y.siteTopology.sheafifiedRepresentable V) :=
  GrothendieckTopology.RepresentableLocalization.baseChangeMap f.base c

/-- The explicit inverse-image `2`-cell of the slice-topos ambient square for the representable
parameter induced by `c`. -/
@[stacks 04J9 "slice-topos square"]
noncomputable def ambientIso :
    Over.star (Y.siteTopology.sheafifiedRepresentable V) ⋙
        ((RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f).localization
          (Y.siteTopology.sheafifiedRepresentable V)).inverseImage ⋙
        Over.pullback (C := Sheaf X.siteTopology (Type (max u v))) (parameter f c) ≅
      (RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f).inverseImage ⋙
        Over.star (X.siteTopology.sheafifiedRepresentable U) :=
  f.localizedAmbientIso (parameter f c)

section StructureCompatibility

variable [X.siteTopology.HasSheafCompose (forget RingCat.{max u v})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{max u v})]

/-- Lemma 18.22.4 (04J9), structure layer: the explicit slice-topos square comparison carries
the ambient structure map to the localized structure map at the representable parameter. -/
@[stacks 04J9 "structure compatibility"]
theorem ambientIso_structure :
    (ambientIso f c).hom.app (RingedSite.Hom.underlyingStructureSheaf Y) ≫
        (Over.star (X.siteTopology.sheafifiedRepresentable U)).map
          f.underlyingInverseImageMap =
      f.localizedUnderlyingInverseImageMap (parameter f c) := sorry

end StructureCompatibility

section Functoriality

variable {V' : Y} {U' : X}
variable (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ f.base.obj V')
variable (h : c' ≫ f.base.map b = a ≫ c)

include h

/-- The representable parameters associated to a commuting square in the two sites form the
commuting square required to localize the inverse-image adjunction. -/
@[stacks 04J9 "representable parameter square"]
theorem parameter_naturality :
    parameter f c' ≫
        (f.base.sheafPullback (Type (max u v))
          Y.siteTopology X.siteTopology).map
            (Y.siteTopology.sheafifiedRepresentableMap b) =
      X.siteTopology.sheafifiedRepresentableMap a ≫ parameter f c := sorry

section StructureCompatibility

variable [X.siteTopology.HasSheafCompose (forget RingCat.{max u v})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{max u v})]

/-- Lemma 18.22.4 (04J9), functorial structure layer: the canonical base-change isomorphism
for the representable parameter square respects the two localized underlying structure maps. -/
@[stacks 04J9 "base-change structure compatibility"]
theorem structureMap_commSq :
    CommSq
      ((LeftExactAdjunction.Localization.inverseImageBaseChangeIso
          (RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f)
          (Y.siteTopology.sheafifiedRepresentableMap b)
          (X.siteTopology.sheafifiedRepresentableMap a)
          (parameter f c) (parameter f c')
          (parameter_naturality f c b a c' h)).hom.app
        ((Over.star (Y.siteTopology.sheafifiedRepresentable V)).obj
          (RingedSite.Hom.underlyingStructureSheaf Y)))
      ((((RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f).localization
          (Y.siteTopology.sheafifiedRepresentable V')).inverseImage ⋙
            Over.pullback (C := Sheaf X.siteTopology (Type (max u v))) (parameter f c')).map
          (((Over.starPullbackIsoStar
            (Y.siteTopology.sheafifiedRepresentableMap b)).app
              (RingedSite.Hom.underlyingStructureSheaf Y)).hom) ≫
        f.localizedUnderlyingInverseImageMap (parameter f c'))
      ((Over.pullback (X.siteTopology.sheafifiedRepresentableMap a)).map
          (f.localizedUnderlyingInverseImageMap (parameter f c)) ≫
        ((Over.starPullbackIsoStar
          (X.siteTopology.sheafifiedRepresentableMap a)).app
            (RingedSite.Hom.underlyingStructureSheaf X)).hom)
      (𝟙 ((Over.star (X.siteTopology.sheafifiedRepresentable U')).obj
        (RingedSite.Hom.underlyingStructureSheaf X))) := sorry

end StructureCompatibility

end Functoriality

section SiteComparison

variable [∀ P : Functor Yᵒᵖ (Type (max u v)), f.base.op.HasLeftKanExtension P]
variable [∀ P : Functor (Over V)ᵒᵖ (Type (max u v)),
  (Over.forget V).op.HasLeftKanExtension P]
variable [∀ P : Functor (Over U)ᵒᵖ (Type (max u v)),
  (Over.forget U).op.HasLeftKanExtension P]

section LocalizedMorphism

variable [X.siteTopology.HasSheafCompose (forget RingCat.{max u v})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{max u v})]

/-- Lemma 18.22.4 (04J9), localized-morphism layer: under the two representable-localization
comparisons, the inverse image of the site-localized morphism is the inverse image localized at
`h_V^#`, followed by pullback along `parameter f c`. -/
@[stacks 04J9 "localized morphism"]
theorem localizedInverseImage :
    IsIsomorphic
      ((f.localizationAt V c).toTopos.inverseImage ⋙
        comparison X.siteTopology U)
      (comparison Y.siteTopology V ⋙
        ((RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f).localization
          (Y.siteTopology.sheafifiedRepresentable V)).inverseImage ⋙
        @Over.pullback (Sheaf X.siteTopology (Type (max u v))) _ _ _
          (parameter f c) (by intro W h; infer_instance)) := sorry

end LocalizedMorphism

/-- Lemma 18.22.4 (04J9), ambient-square layer: after the representable-localization
comparisons, the upper-right path of the slice-site square agrees with the left-lower path of
the slice-topos square at `parameter f c`. -/
@[stacks 04J9 "ambient square comparison"]
theorem ambientSquare :
    IsIsomorphic
      ((RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f).inverseImage ⋙
        X.siteTopology.overPullback (Type (max u v)) U ⋙
        comparison X.siteTopology U)
      (Y.siteTopology.overPullback (Type (max u v)) V ⋙
        comparison Y.siteTopology V ⋙
        ((RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f).localization
          (Y.siteTopology.sheafifiedRepresentable V)).inverseImage ⋙
        Over.pullback (C := Sheaf X.siteTopology (Type (max u v))) (parameter f c)) := sorry

end SiteComparison

section SiteFunctoriality

variable [X.siteTopology.HasSheafCompose (forget RingCat.{max u v})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{max u v})]

variable {V' : Y} {U' : X}
variable (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ f.base.obj V')
variable (h : c' ≫ f.base.map b = a ≫ c)
variable [∀ P : Functor Yᵒᵖ (Type (max u v)), f.base.op.HasLeftKanExtension P]
variable [∀ P : Functor (Over V')ᵒᵖ (Type (max u v)),
  (Over.forget V').op.HasLeftKanExtension P]
variable [∀ P : Functor (Over U')ᵒᵖ (Type (max u v)),
  (Over.forget U').op.HasLeftKanExtension P]

include h

/-- Lemma 18.22.4 (04J9), relocalization-square layer: for a commuting square
`c' ≫ f.base.map b = a ≫ c`, the upper-right path of the slice-site square agrees, under
representable localization, with the left-lower path of the slice-topos base-change square. -/
@[stacks 04J9 "relocalization square comparison"]
theorem relocalizationSquare :
    IsIsomorphic
      ((f.localizationAt V c).toTopos.inverseImage ⋙
        X.siteTopology.overMapPullback (Type (max u v)) a ⋙
        comparison X.siteTopology U')
      (Y.siteTopology.overMapPullback (Type (max u v)) b ⋙
        comparison Y.siteTopology V' ⋙
        ((RingedSite.Hom.toMorphismOfTopoi.{u, v, u, v, max u v, max u v} f).localization
          (Y.siteTopology.sheafifiedRepresentable V')).inverseImage ⋙
        @Over.pullback (Sheaf X.siteTopology (Type (max u v))) _ _ _
          (parameter f c') (by intro W h; infer_instance)) := sorry

end SiteFunctoriality

end RingedSite.Localization.Representable
