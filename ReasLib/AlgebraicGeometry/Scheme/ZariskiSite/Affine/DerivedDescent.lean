/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Empty
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.MayerVietoris
public import ReasLib.CategoryTheory.Sites.TopologyComparison.AbsoluteDerived
public import ReasLib.CategoryTheory.Sites.Derived.Sections.MayerVietoris

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineZariski

/-- The affine Zariski derived descent criterion for the chaotic-to-Zariski comparison. -/
theorem essImage_iff {X : Scheme.{u}}
    [HasWeakSheafify X.smallAffineZariskiTopology AddCommGrpCat.{u}]
    [HasSheafify X.smallAffineZariskiTopology AddCommGrpCat.{u}]
    [HasSheafify (⊥ : GrothendieckTopology X.smallAffineZariskiSite) AddCommGrpCat.{u}]
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (Absolute.pushforward
        (bot_le : (⊥ : GrothendieckTopology X.smallAffineZariskiSite) ≤
          X.smallAffineZariskiTopology)))
      (Absolute.qis X.smallAffineZariskiTopology)]
    (K : DerivedCategory.Plus
      (SiteAbelianSheafCat (⊥ : GrothendieckTopology X.smallAffineZariskiSite))) :
    Functor.essImage
        (Absolute.rightDerived
          (bot_le : (⊥ : GrothendieckTopology X.smallAffineZariskiSite) ≤
            X.smallAffineZariskiTopology))
        (DerivedCategory.Plus.ι.obj K) ↔
      IsZero
          ((siteAbelianSectionsDerived
              (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
              (empty X)).obj
            (DerivedCategory.Plus.ι.obj K)) ∧
        ∀ (S : Square X.smallAffineZariskiSite),
          IsStandardOpenSquare S →
            S.Condition (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
              (DerivedCategory.Plus.ι.obj K) := sorry

end AlgebraicGeometry.Scheme.AffineZariski

end
