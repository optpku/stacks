/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.CompletedGaloisSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Cohomology
public import ReasLib.RepresentationTheory.Homological.ContCohomology.Abelian

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Scalar one acts trivially on completed-sheaf cohomology. -/
theorem completedCohomology_smul_one
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) (x : proEtaleCohomology (Spec (.of K))
      (completedGaloisSheaf K Ksep I M) i) :
    proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M 1) i x = x := sorry

/-- Scalar multiplication on completed-sheaf cohomology is associative. -/
theorem completedCohomology_smul_mul
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) (r s : Λ) (x : proEtaleCohomology (Spec (.of K))
      (completedGaloisSheaf K Ksep I M) i) :
    proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M (r * s)) i x =
      proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M r) i
        (proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M s) i x) := sorry

/-- Scalar multiplication on completed-sheaf cohomology preserves zero. -/
theorem completedCohomology_smul_zero
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) (r : Λ) :
    proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M r) i 0 = 0 := sorry

/-- Scalar multiplication on completed-sheaf cohomology is additive. -/
theorem completedCohomology_smul_add
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) (r : Λ) (x y : proEtaleCohomology (Spec (.of K))
      (completedGaloisSheaf K Ksep I M) i) :
    proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M r) i (x + y) =
      proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M r) i x +
        proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M r) i y := sorry

/-- Addition of coefficients is addition of completed-sheaf endomorphisms. -/
theorem completedCohomology_add_smul
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) (r s : Λ) (x : proEtaleCohomology (Spec (.of K))
      (completedGaloisSheaf K Ksep I M) i) :
    proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M (r + s)) i x =
      proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M r) i x +
        proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M s) i x := sorry

/-- The zero coefficient acts trivially on completed-sheaf cohomology. -/
theorem completedCohomology_zero_smul
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) (x : proEtaleCohomology (Spec (.of K))
      (completedGaloisSheaf K Ksep I M) i) :
    proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M 0) i x = 0 := sorry

/-- Scalar multiplication on completed-sheaf cohomology is induced by the
corresponding sheaf endomorphisms. -/
public instance module_proEtaleCohomology_completedGaloisSheaf
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (Λ : Type u) [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M]
    [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] (i : ℕ) :
    Module Λ (proEtaleCohomology (Spec (.of K)) (completedGaloisSheaf K Ksep I M) i) where
  smul r x := proEtaleCohomologyMap (completedGaloisSheaf_smul K Ksep I M r) i x
  one_smul := completedCohomology_smul_one K Ksep I M i
  mul_smul := completedCohomology_smul_mul K Ksep I M i
  smul_zero := completedCohomology_smul_zero K Ksep I M i
  smul_add := completedCohomology_smul_add K Ksep I M i
  add_smul := completedCohomology_add_smul K Ksep I M i
  zero_smul := completedCohomology_zero_smul K Ksep I M i

/-- The profinite completed Galois sheaf computes continuous cohomology in
every cohomological degree. -/
theorem profiniteGaloisSheaf_proetaleCohomology
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
    [TotallyDisconnectedSpace M] [DistribMulAction (Gal(Ksep / K)) M]
    [ContinuousSMul (Gal(Ksep / K)) M] (i : ℕ) :
    IsIsomorphic
      (proEtaleCohomology (Spec (.of K)) (profiniteGaloisSheaf K Ksep M) i)
      (ContinuousCohomology.abelian (Gal(Ksep / K))
        (ContinuousModule.profiniteTopRep (Gal(Ksep / K)) M) i) := sorry

/-- The completed Galois sheaf computes continuous cohomology as a module over
the coefficient ring in every degree. -/
theorem completedGaloisSheaf_proetaleCohomology
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction (Gal(Ksep / K)) M]
    [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) :
    IsIsomorphic
      (ModuleCat.of Λ
        (proEtaleCohomology (Spec (.of K)) (completedGaloisSheaf K Ksep I M) i))
      (ModuleCat.of Λ
        (ContinuousCohomology.abelian (Gal(Ksep / K))
          (ContinuousModule.adicTopRep (Gal(Ksep / K)) I M) i)) := sorry

end AlgebraicGeometry.Scheme.ProEt

end
