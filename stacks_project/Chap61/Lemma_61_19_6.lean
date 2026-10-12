/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import stacks_project.Chap61.Lemma_61_19_5_Adjunction
public import stacks_project.Chap61.Remark_61_14_4_Sections
import Mathlib.Tactic.CrossRefAttribute

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
variable [PreservesFiniteLimits (etaleToProEtPullback X AddCommGrpCat.{u + 1})]
variable [PreservesFiniteColimits (etaleToProEtPullback X AddCommGrpCat.{u + 1})]
variable [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))]
variable [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor (ProEt.topology X) (ProEt.globalProEt X)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}))]

/-- Lemma 61.19.6 (1): for a scheme `X` and an abelian sheaf `F` on `X.Etale`,
`H^i(X.Etale, F)` is isomorphic to `H^i(X.ProEt, ε⁻¹ F)` for every `i`.
Here `H^i` is `DerivedCategory.Plus.homologyFunctor` of bounded-below
`RΓ` at `globalEtale X` and `ProEt.globalProEt X`, and `ε⁻¹` is
`etaleToProEt_plusPullback` applied to `F[0]`. -/
@[stacks 099W]
theorem etaleToProEtPullback_cohomology_isIsomorphic
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    IsIsomorphic
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((siteAbelianSectionsBoundedBelowDerived
            X.smallEtaleTopology (globalEtale X)).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)))
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((siteAbelianSectionsBoundedBelowDerived
            (ProEt.topology X) (ProEt.globalProEt X)).obj
          ((etaleToProEt_plusPullback X).obj
            ((DerivedCategory.Plus.singleFunctor
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)))) :=
  sorry

/-- Lemma 61.19.6 (2): for a scheme `X` and `K` in `D⁺(X.Etale)`,
`RΓ(X.Etale, K)` is isomorphic to `RΓ(X.ProEt, ε⁻¹ K)`. Here `RΓ` is
`siteAbelianSectionsBoundedBelowDerived` at `globalEtale X` and
`ProEt.globalProEt X`, and `ε⁻¹` is `etaleToProEt_plusPullback`. -/
@[stacks 099W]
theorem etaleToProEt_plusPullback_globalSections_isIsomorphic
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived
          X.smallEtaleTopology (globalEtale X)).obj K)
      ((siteAbelianSectionsBoundedBelowDerived
          (ProEt.topology X) (ProEt.globalProEt X)).obj
        ((etaleToProEt_plusPullback X).obj K)) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
