/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Exactness
public import ReasLib.CategoryTheory.Sites.Over.Derived.Unbounded

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable {S T : Scheme.{u}}

/-- Derived restriction from the big étale site of a scheme to its small étale site. -/
noncomputable abbrev relocalization (g : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}] :
    DerivedCategory (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  siteAbelianInverseImageDerived T.smallEtaleTopology
    (S.overGrothendieckTopology @Etale) (relocalizationFunctor g)

/-- Restriction of a big étale derived direct image agrees with small-site direct image. -/
theorem directImageRestrict
    (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).Additive]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1})) :
    IsIsomorphic ((relocalization (𝟙 S)).obj
        ((CategoryTheory.GrothendieckTopology.Derived.Over.pushforward
          Scheme.etaleTopology f).obj K))
      ((AlgebraicGeometry.Scheme.Etale.Derived.directImage f).obj
        ((relocalization (𝟙 T)).obj K)) := sorry

/-- Derived restriction commutes with direct image across an arbitrary cartesian square. -/
theorem directImageRelocalization
    {S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (g' : T' ⟶ T) (f' : T' ⟶ S') (hcart : IsPullback g' f' f g)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (T'.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (S'.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [((smallEtalePullback f').sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S'.smallEtaleTopology T'.smallEtaleTopology).Additive]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over T')ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f').op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1})) :
    IsIsomorphic ((relocalization g).obj
        ((CategoryTheory.GrothendieckTopology.Derived.Over.pushforward
          Scheme.etaleTopology f).obj K))
      ((AlgebraicGeometry.Scheme.Etale.Derived.directImage f').obj
        ((relocalization g').obj K)) := sorry

/-- Pullback from the small étale site to the big étale site identifies derived cohomology with
sections on the small étale site. -/
theorem etaleCohomology_piInverseImage
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
          (Over.mk (𝟙 S))).obj
            ((siteAbelianPullbackDerived S.smallEtaleTopology
              (S.overGrothendieckTopology @Etale) (relocalizationFunctor (𝟙 S))).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived S.smallEtaleTopology
          (terminal S.Etale)).obj K)) := sorry

/-- The derived inverse image along a scheme morphism identifies the corresponding big and small
étale cohomology groups. -/
theorem etaleCohomology_smallInverseImage
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((smallEtalePullback f).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          (T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
          (Over.mk f)).obj
            ((siteAbelianPullbackDerived S.smallEtaleTopology
              (S.overGrothendieckTopology @Etale) (relocalizationFunctor (𝟙 S))).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived T.smallEtaleTopology
          (terminal T.Etale)).obj
            ((siteAbelianPullbackDerived S.smallEtaleTopology
              T.smallEtaleTopology (smallEtalePullback f)).obj K))) := sorry

/-- Relocalization from the big étale site to the small étale site identifies derived cohomology. -/
theorem etaleCohomology_relocalization
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    (M : DerivedCategory
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
          (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived T.smallEtaleTopology
          (terminal T.Etale)).obj
          ((siteAbelianInverseImageDerived T.smallEtaleTopology
            (S.overGrothendieckTopology @Etale)
            (relocalizationFunctor f)).obj M))) := sorry

end AlgebraicGeometry.Scheme.Etale.Derived

end
