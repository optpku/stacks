/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Cech.StandardCover

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.SmallStandardTopology
  CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-! Lemma 59.22.1: finite standard affine coverings may be replaced by their
coproduct singleton, with the corresponding Čech comparison statements. -/

/- Lemma 59.22.1 (1): the coproduct of a finite standard affine covering is affine. -/
@[stacks 03OZ] #check (AlgebraicGeometry.standardCover_coproduct_isAffine :
    ∀ (τ : StandardTopology) {T : Scheme.{u}}
    (family : AffineFamilyOver T) (hfamily : τ.IsCover family)
    [HasCoproduct family.U],
    IsAffine (∐ family.U))

/- Lemma 59.22.1 (2): the coproduct singleton of a finite standard affine covering is fpqc. -/
@[stacks 03OZ] #check (AlgebraicGeometry.standardCover_coproduct_fpqcCovering :
    ∀ (τ : StandardTopology) {T : Scheme.{u}}
    (family : AffineFamilyOver T) (hfamily : τ.IsCover family)
    [HasCoproduct family.U],
    Scheme.FpqcCovering (fun _ : PUnit ↦ Over.mk (Sigma.desc family.map)))

/- Lemma 59.22.1 (3): away from the Zariski topology, the coproduct singleton is also a
standard covering. -/
@[stacks 03OZ] #check (AlgebraicGeometry.standardCover_coproduct_covering :
    ∀ (τ : StandardTopology) {T : Scheme.{u}}
    (family : AffineFamilyOver T) (hfamily : τ.IsCover family)
    [HasCoproduct family.U] (hτ : τ ≠ .zariski),
    Presieve.ofArrows (fun _ : PUnit ↦ ∐ family.U)
      (fun _ ↦ Sigma.desc family.map) ∈ τ.precoverage.coverings T)

/- Lemma 59.22.1 (4): the finite-family and coproduct-singleton Čech complexes agree on the
big standard site. -/
@[stacks 03OZ] #check (AlgebraicGeometry.standardCover_cechMap_isIso :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (U : Over S) (n : ℕ)
    (family : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((Over.forget S).obj ((family i).left)))
    (h_cover : τ.IsCover
      (AffineFamilyOver.ofSiteFamily (Over.forget S) U n family h_affine))
    [HasCoproduct (fun i ↦ (family i).left)]
    (F : Sheaf (τ.overTopology S) AddCommGrpCat.{u}),
    IsIso (cechComplexMapOfRefinement U
      (FormalCoproduct.Over.coproductSingleton
        (FormalCoproduct.mk (Fin n) family)).obj
      (FormalCoproduct.mk (Fin n) family).obj
      (FormalCoproduct.Over.toCoproductSingleton
        (FormalCoproduct.mk (Fin n) family)) F.obj))

/- Lemma 59.22.1 (5): the finite-family and coproduct-singleton Čech complexes agree on the
small étale site. -/
@[stacks 03OZ] #check (AlgebraicGeometry.standardCover_smallEtale_cechMap_isIso :
    ∀ (S : Scheme.{u}) (U : S.Etale) (n : ℕ)
    (family : Fin n → Over U)
    (h_affine : ∀ i, IsAffine
      ((etale.toScheme S).obj ((family i).left)))
    (h_cover : etale.toStandard.IsCover
      (AffineFamilyOver.ofSiteFamily
        (etale.toScheme S) U n family h_affine))
    [HasCoproduct (fun i ↦ (family i).left)]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}),
    IsIso (cechComplexMapOfRefinement U
      (FormalCoproduct.Over.coproductSingleton
        (FormalCoproduct.mk (Fin n) family)).obj
      (FormalCoproduct.mk (Fin n) family).obj
      (FormalCoproduct.Over.toCoproductSingleton
        (FormalCoproduct.mk (Fin n) family)) F.obj))

end AlgebraicGeometry
