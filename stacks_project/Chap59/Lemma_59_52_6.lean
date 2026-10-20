/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.Coproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    Y.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable {I : Type u}
variable (K : I → DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
variable [QuasiCompact f] [QuasiSeparated f]

/- Lemma 59.52.6: if `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism of
schemes and `K_i ∈ D(X_étale)` is a family uniformly bounded below, then derived
pushforward `Rf_*` (`etaleAbelianPushforwardDerived f`) commutes with coproducts.
If `H^n(K_i) = 0` for all `n < a` (equivalently `(K i).IsGE a`), then the comparison
`⊕_i Rf_* K_i ⟶ Rf_* (⊕_i K_i)` is an isomorphism in `D(Y_étale)`. -/
@[stacks 0GIW] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedPushforward_preservesCoproduct f K :
    ∀ (a : ℤ), (∀ i : I, DerivedCategory.IsGE (K i) a) →
      IsIso (CategoryTheory.Limits.sigmaComparison (etaleAbelianPushforwardDerived f) K))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedPushforward_preservesCoproduct_homology f K :
    ∀ (a : ℤ), (∀ i : I, DerivedCategory.IsGE (K i) a) → ∀ (p : ℤ),
      IsIso ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) p).map
          (CategoryTheory.Limits.sigmaComparison (etaleAbelianPushforwardDerived f) K)))

#check (CategoryTheory.Limits.sigmaComparison (etaleAbelianPushforwardDerived f) K :
  (∐ fun i : I ↦ (etaleAbelianPushforwardDerived f).obj (K i)) ⟶
    (etaleAbelianPushforwardDerived f).obj (∐ K))

#check (CategoryTheory.Limits.ι_comp_sigmaComparison
  (etaleAbelianPushforwardDerived f) K :
  ∀ i : I,
    Sigma.ι (fun j : I ↦ (etaleAbelianPushforwardDerived f).obj (K j)) i ≫
        CategoryTheory.Limits.sigmaComparison (etaleAbelianPushforwardDerived f) K =
      (etaleAbelianPushforwardDerived f).map (Sigma.ι K i))

end AlgebraicGeometry.Scheme.Etale

end
