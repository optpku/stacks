/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleDerivedSections
import StacksCheckRecall

/-!
# Lemma 61.19.6

Abelian étale cohomology agrees with pro-étale cohomology of `ε⁻¹ F`, and
bounded-below derived global sections on `X.Etale` agree with those of
`ε⁻¹ K` on `X.ProEt`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]
variable [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))]
variable [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor (ProEt.topology X) (ProEt.globalProEt X)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}))]

/- Lemma 61.19.6 (1): for a scheme `X` and an abelian sheaf `F` on `X.Etale`,
`H^i(X.Etale, F)` is isomorphic to `H^i(X.ProEt, ε⁻¹ F)` for every `i`.
Here `H^i` is `DerivedCategory.Plus.homologyFunctor` of bounded-below
`RΓ` at `Etale.globalEtale X` and `ProEt.globalProEt X`, and `ε⁻¹` is
`etaleToProEtPullback` applied to the coefficient sheaf. -/
@[stacks 099W]
#check (AlgebraicGeometry.Scheme.etaleToProEtPullback_cohomology_isIsomorphic X :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ),
    IsIsomorphic
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((siteAbelianSectionsBoundedBelowDerived
            X.smallEtaleTopology (Etale.globalEtale X)).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)))
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((siteAbelianSectionsBoundedBelowDerived
            (ProEt.topology X) (ProEt.globalProEt X)).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) (0 : ℤ)).obj
            ((etaleToProEtPullback X AddCommGrpCat.{u + 1}).obj F)))))

/- Lemma 61.19.6 (2): for a scheme `X` and `K` in `D⁺(X.Etale)`,
`RΓ(X.Etale, K)` is isomorphic to `RΓ(X.ProEt, ε⁻¹ K)`. Here `RΓ` is
`siteAbelianSectionsBoundedBelowDerived` at `Etale.globalEtale X` and
`ProEt.globalProEt X`, and `ε⁻¹` is `etaleToProEt_plusPullback`. -/
@[stacks 099W]
#check (AlgebraicGeometry.Scheme.etaleToProEt_plusPullback_globalSections_isIsomorphic X :
    ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived
          X.smallEtaleTopology (Etale.globalEtale X)).obj K)
      ((siteAbelianSectionsBoundedBelowDerived
          (ProEt.topology X) (ProEt.globalProEt X)).obj
        ((etaleToProEt_plusPullback X).obj K)))

end AlgebraicGeometry.Scheme

end

end
