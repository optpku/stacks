/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.WContractibleCover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 61.13.3: let Sch_proétale be a big pro-étale site as in
Definition 61.12.7. For every object T of Sch_proétale there exists a
covering {T_i ⟶ T} in Sch_proétale with each T_i affine and the spectrum
of a w-contractible ring. In particular, T_i is weakly contractible in
Sch_proétale. -/
@[stacks 098I] #check
  (AlgebraicGeometry.BigProetaleSite.exists_affine_wContractibleRing_cover :
    ∀ (X : AlgebraicGeometry.BigProetaleSite.{u}) (T : X.carrier),
      ∃ 𝒰 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Presieve.ofArrows
            (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) ∈
            (@CategoryTheory.Pretopology.toPrecoverage _ _ X.hasPullbacks X.pretopology) T ∧
          ∀ i, AlgebraicGeometry.IsAffine (X.toScheme.obj (𝒰.obj i).left) ∧
            IsWContractibleRing.{u, u} Γ(X.toScheme.obj (𝒰.obj i).left, ⊤) ∧
            X.toGrothendieck.IsWeaklyContractible (𝒰.obj i).left)

#check
  (AlgebraicGeometry.BigProetaleSite.exists_affine_weaklyContractible_cover :
    ∀ (X : AlgebraicGeometry.BigProetaleSite.{u}) (T : X.carrier),
      ∃ 𝒰 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Presieve.ofArrows
            (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) ∈
            (@CategoryTheory.Pretopology.toPrecoverage _ _ X.hasPullbacks X.pretopology) T ∧
          ∀ i, AlgebraicGeometry.IsAffine (X.toScheme.obj (𝒰.obj i).left) ∧
            X.toGrothendieck.IsWeaklyContractible (𝒰.obj i).left)

#check
  (AlgebraicGeometry.BigProetaleSite.hasEnough_isAffine_isWContractibleRing :
    ∀ X : AlgebraicGeometry.BigProetaleSite.{u},
      X.toGrothendieck.HasEnoughObjectsWithProperty
        (fun T ↦ AlgebraicGeometry.IsAffine (X.toScheme.obj T) ∧
          IsWContractibleRing.{u, u} Γ(X.toScheme.obj T, ⊤)))

#check
  (AlgebraicGeometry.Scheme.Proetale.exists_affine_wContractibleRing_cover :
    ∀ T : AlgebraicGeometry.Scheme.{u},
      ∃ 𝒰 : T.Cover.{u} AlgebraicGeometry.Scheme.proetalePrecoverage,
        ∀ i, AlgebraicGeometry.IsAffine (𝒰.X i) ∧
          IsWContractibleRing.{u, u} Γ(𝒰.X i, ⊤))

#check
  (AlgebraicGeometry.Scheme.Proetale.exists_affineCover_isWContractibleRing :
    ∀ T : AlgebraicGeometry.Scheme.{u},
      ∃ 𝒰 : T.AffineCover.{u} (@AlgebraicGeometry.WeaklyEtale),
        CategoryTheory.Presieve.ofArrows
            (fun j ↦ AlgebraicGeometry.Spec (𝒰.X j)) 𝒰.f ∈
            AlgebraicGeometry.Scheme.proetalePrecoverage T ∧
          ∀ j, IsWContractibleRing.{u, u} (𝒰.X j))
