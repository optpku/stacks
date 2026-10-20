module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.SmallEtale
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ZariskiComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski.Flat
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Exact derived pullback to the small étale site

Exact pullback along the canonical étale-to-Zariski morphism induces an equivalence
between the full derived subcategories with quasi-coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open AlgebraicGeometry.Scheme.SiteRestriction
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace DerivedQCoh

/-- Pullback from Zariski module sheaves to étale module sheaves, bundled with its
canonical exactness certificate. -/
noncomputable def epsilonModulePullback (X : Scheme.{u}) :
    SheafOfModules.{u} (Zariski.Small.structureSheaf X) ⥤ₑ
      SheafOfModules.{u} (Etale.Small.structureSheaf X) :=
  ⟨(smallEtaleToZariski X).modulePullback.{u},
    smallEtaleToZariski_modulePullback_exact X⟩

/-- The underlying functor of the exact étale pullback is canonical module pullback. -/
@[simp]
theorem epsilonModulePullback_obj (X : Scheme.{u}) :
    (epsilonModulePullback X).obj = (smallEtaleToZariski X).modulePullback.{u} := rfl

namespace zariskiEpsilonStar

/-- Exact pullback along `ε` preserves quasi-coherent cohomology. -/
theorem mapsTo (X : Scheme.{u}) :
    zariskiSiteProperty X ≤
      (smallEtaleProperty X).inverseImage
        (epsilonModulePullback X).mapDerivedCategory :=
  sorry

end zariskiEpsilonStar

/-- Exact derived pullback `ε^*` along the morphism of ringed sites from the small étale
site of `X` to its small Zariski site, restricted to complexes with quasi-coherent
cohomology. -/
noncomputable def zariskiEpsilonStar (X : Scheme.{u}) :
    ZariskiSite X ⥤ SmallEtale X :=
  ObjectProperty.FullSubcategory.restrict
    (epsilonModulePullback X).mapDerivedCategory
    (zariskiEpsilonStar.mapsTo X)

namespace zariskiEpsilonStar

/-- Forgetting quasi-coherence after site-level `ε^*` recovers ambient exact derived
pullback. -/
noncomputable def inclusionIso (X : Scheme.{u}) :
    zariskiEpsilonStar X ⋙ SmallEtale.inclusion X ≅
      ZariskiSite.inclusion X ⋙
        (epsilonModulePullback X).mapDerivedCategory :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (epsilonModulePullback X).mapDerivedCategory
    (mapsTo X)

/-- The underlying derived module of site-level `ε^*` is ambient exact derived pullback. -/
@[simp]
theorem obj_obj (X : Scheme.{u}) (E : ZariskiSite X) :
    ((zariskiEpsilonStar X).obj E).obj =
      ((epsilonModulePullback X).mapDerivedCategory).obj E.obj :=
  rfl

end zariskiEpsilonStar

/-- Site-level exact derived pullback along `ε` is an equivalence on complexes with
quasi-coherent cohomology. -/
instance zariskiEpsilonStar_isEquivalence (X : Scheme.{u}) :
    (zariskiEpsilonStar X).IsEquivalence := sorry

/-- Exact derived pullback `ε^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_étale)` obtained by comparing
the scheme category with the small Zariski site and then applying exact pullback along
`smallEtaleToZariski`. -/
noncomputable def epsilonStar (X : Scheme.{u}) :
    DerivedQCoh X ⥤ SmallEtale X :=
  schemeToZariski X ⋙ zariskiEpsilonStar X

namespace epsilonStar

/-- The composite `ε^*` preserves quasi-coherent cohomology in the sense that it lands in
`SmallEtale`. -/
theorem mapsTo (X : Scheme.{u}) (E : DerivedQCoh X) :
    smallEtaleProperty X ((SmallEtale.inclusion X).obj ((epsilonStar X).obj E)) :=
  ((epsilonStar X).obj E).property

/-- Forgetting quasi-coherence after composite `ε^*` recovers the ambient derived
comparison followed by exact pullback along `ε`. -/
noncomputable def inclusionIso (X : Scheme.{u}) :
    epsilonStar X ⋙ SmallEtale.inclusion X ≅
      DerivedQCoh.inclusion X ⋙
        (schemeToZariskiDerived X ⋙
          (epsilonModulePullback X).mapDerivedCategory) :=
  (Functor.associator (schemeToZariski X) (zariskiEpsilonStar X)
      (SmallEtale.inclusion X)).symm.trans
    ((Functor.isoWhiskerLeft (schemeToZariski X) (zariskiEpsilonStar.inclusionIso X)).trans
      ((Functor.associator (schemeToZariski X) (ZariskiSite.inclusion X)
          (epsilonModulePullback X).mapDerivedCategory).trans
        ((Functor.isoWhiskerRight (schemeToZariski.inclusionIso X)
            (epsilonModulePullback X).mapDerivedCategory).trans
          (Functor.associator (DerivedQCoh.inclusion X) (schemeToZariskiDerived X)
            (epsilonModulePullback X).mapDerivedCategory).symm)))

/-- The underlying derived module of composite `ε^*` is ambient exact derived pullback of
the Zariski comparison of `E`. -/
@[simp]
theorem obj_obj (X : Scheme.{u}) (E : DerivedQCoh X) :
    ((epsilonStar X).obj E).obj =
      ((epsilonModulePullback X).mapDerivedCategory).obj
        ((schemeToZariskiDerived X).obj E.obj) :=
  rfl

end epsilonStar

/-- Exact derived pullback along `ε` is an equivalence `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_étale)`. -/
instance epsilonStar_isEquivalence (X : Scheme.{u}) :
    (epsilonStar X).IsEquivalence :=
  Functor.isEquivalence_trans (schemeToZariski X) (zariskiEpsilonStar X)


end DerivedQCoh

end AlgebraicGeometry.Scheme
