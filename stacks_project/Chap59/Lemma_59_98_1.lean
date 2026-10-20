/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.DerivedDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

/- Lemma 59.98.1. For `K` in `D⁺` of abelian sheaves on the chaotic site `X_affine`, `K` lies in
the essential image of the fully faithful functor `Rε_* : D(X_affine,Zar) ⟶ D(X_affine)` if and
only if `RΓ(∅, K)` is zero in `D(Ab)` and every affine standard-open Mayer--Vietoris square
satisfies the canonical comparison condition. -/
@[stacks 0F1L] #check (AlgebraicGeometry.Scheme.AffineZariski.essImage_iff :
  ∀ {X : Scheme},
    [HasWeakSheafify X.smallAffineZariskiTopology AddCommGrpCat] →
    [HasSheafify X.smallAffineZariskiTopology AddCommGrpCat] →
    [HasSheafify (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
      AddCommGrpCat] →
    (K : DerivedCategory.Plus
      (SiteAbelianSheafCat
        (⊥ : GrothendieckTopology X.smallAffineZariskiSite))) →
    Functor.essImage
        (Absolute.rightDerived
          (bot_le : (⊥ : GrothendieckTopology X.smallAffineZariskiSite) ≤
            X.smallAffineZariskiTopology))
        (DerivedCategory.Plus.ι.obj K) ↔
      IsZero
          ((siteAbelianSectionsDerived
              (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
              (AffineZariski.empty X)).obj
            (DerivedCategory.Plus.ι.obj K)) ∧
        ∀ (S : GrothendieckTopology.Derived.Sections.MayerVietoris.Square
            X.smallAffineZariskiSite),
          AffineZariski.IsStandardOpenSquare S →
            S.Condition (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
              (DerivedCategory.Plus.ι.obj K))

end
