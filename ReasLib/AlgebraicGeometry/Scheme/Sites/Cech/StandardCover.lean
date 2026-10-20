/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Site
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Cech.CoproductSingleton
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small

@[expose] public section

open AlgebraicGeometry.SmallStandardTopology CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- On the big standard site, the Čech comparison from the coproduct singleton of a
finite standard affine covering to the original family is an isomorphism for abelian sheaves. -/
theorem standardCover_cechMap_isIso
    (τ : StandardTopology) (S : Scheme.{u}) (U : Over S) (n : ℕ)
    (family : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((Over.forget S).obj ((family i).left)))
    (h_cover : τ.IsCover
      (AffineFamilyOver.ofSiteFamily (Over.forget S) U n family h_affine))
    [HasCoproduct (fun i ↦ (family i).left)]
    (F : Sheaf (τ.overTopology S) AddCommGrpCat.{u}) :
    IsIso (cechComplexMapOfRefinement U
      (FormalCoproduct.Over.coproductSingleton
        (FormalCoproduct.mk (Fin n) family)).obj
      (FormalCoproduct.mk (Fin n) family).obj
      (FormalCoproduct.Over.toCoproductSingleton
        (FormalCoproduct.mk (Fin n) family)) F.obj) := sorry

/-- On the small étale site, the Čech comparison from the coproduct singleton of a
finite standard affine covering to the original family is an isomorphism for abelian sheaves. -/
theorem standardCover_smallEtale_cechMap_isIso
    (S : Scheme.{u}) (U : S.Etale) (n : ℕ)
    (family : Fin n → Over U)
    (h_affine : ∀ i, IsAffine
      ((etale.toScheme S).obj ((family i).left)))
    (h_cover : etale.toStandard.IsCover
      (AffineFamilyOver.ofSiteFamily
        (etale.toScheme S) U n family h_affine))
    [HasCoproduct (fun i ↦ (family i).left)]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (cechComplexMapOfRefinement U
      (FormalCoproduct.Over.coproductSingleton
        (FormalCoproduct.mk (Fin n) family)).obj
      (FormalCoproduct.mk (Fin n) family).obj
      (FormalCoproduct.Over.toCoproductSingleton
        (FormalCoproduct.mk (Fin n) family)) F.obj) := sorry

end AlgebraicGeometry
