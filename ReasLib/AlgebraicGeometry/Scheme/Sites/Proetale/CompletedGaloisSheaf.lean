/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.EtalePullback
public import ReasLib.RepresentationTheory.Continuous.Quotients

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The pulled-back inverse system of adic discrete Galois sheaves. -/
def completedGaloisSystem (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] :
    ℕᵒᵖ ⥤ Sheaf (topology (Spec (.of K))) AddCommGrpCat.{u} :=
  ContinuousModule.adicQuotientSystem (Gal(Ksep / K)) I M ⋙
    GaloisCohomology.discreteSheaf K Ksep ⋙ etaleSheafPullback (Spec (.of K))

/-- The completed Galois sheaf is the inverse limit of its adic stages. -/
public def completedGaloisSheaf (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] :
    Sheaf (topology (Spec (.of K))) AddCommGrpCat.{u} :=
  limit (completedGaloisSystem K Ksep I M)

/-- The projection from the completed sheaf to its `n`th stage. -/
def completedGaloisSheaf_π (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) :
    completedGaloisSheaf K Ksep I M ⟶
      (completedGaloisSystem K Ksep I M).obj (op n) :=
  limit.π (completedGaloisSystem K Ksep I M) (op n)

/-- The completed sheaf satisfies the inverse-limit universal property. -/
def completedGaloisSheaf_isLimit (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] :
    IsLimit (limit.cone (completedGaloisSystem K Ksep I M)) :=
  limit.isLimit (completedGaloisSystem K Ksep I M)

/-- Scalar multiplication on the completed sheaf is induced stagewise. -/
public def completedGaloisSheaf_smul (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    completedGaloisSheaf K Ksep I M ⟶ completedGaloisSheaf K Ksep I M :=
  limMap
    (Functor.whiskerRight (ContinuousModule.adicQuotientSystem_smul (Gal(Ksep / K)) I M r)
      (GaloisCohomology.discreteSheaf K Ksep ⋙ etaleSheafPullback (Spec (.of K))))

/-- Scalar one acts as the identity on the completed sheaf. -/
theorem completedGaloisSheaf_smul_one (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] :
    completedGaloisSheaf_smul K Ksep I M 1 = 𝟙 (completedGaloisSheaf K Ksep I M) := sorry

/-- Addition of scalars is addition of sheaf endomorphisms. -/
theorem completedGaloisSheaf_smul_add (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] (r t : Λ) :
    completedGaloisSheaf_smul K Ksep I M (r + t) =
      completedGaloisSheaf_smul K Ksep I M r + completedGaloisSheaf_smul K Ksep I M t := sorry

/-- Multiplication of scalars is composition of sheaf endomorphisms. -/
theorem completedGaloisSheaf_smul_mul (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction (Gal(Ksep / K)) M] [SMulCommClass (Gal(Ksep / K)) Λ M]
    [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)] (r t : Λ) :
    completedGaloisSheaf_smul K Ksep I M (r * t) =
      completedGaloisSheaf_smul K Ksep I M t ≫ completedGaloisSheaf_smul K Ksep I M r := sorry

/-- The pulled-back inverse system of finite discrete Galois sheaves. -/
def profiniteGaloisSystem (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction (Gal(Ksep / K)) M]
    [ContinuousSMul (Gal(Ksep / K)) M] :
    (ContinuousModule.IsFiniteGaloisQuotient (Gal(Ksep / K)) M).FullSubcategory ⥤
      Sheaf (topology (Spec (.of K))) AddCommGrpCat.{u} :=
  ContinuousModule.profiniteQuotientSystem (Gal(Ksep / K)) M ⋙
    GaloisCohomology.discreteSheaf K Ksep ⋙ etaleSheafPullback (Spec (.of K))

/-- The profinite completed Galois sheaf is the limit of finite stages. -/
public def profiniteGaloisSheaf (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction (Gal(Ksep / K)) M]
    [ContinuousSMul (Gal(Ksep / K)) M] :
    Sheaf (topology (Spec (.of K))) AddCommGrpCat.{u} :=
  limit (profiniteGaloisSystem K Ksep M)

/-- The projection from the profinite completed sheaf to a finite stage. -/
def profiniteGaloisSheaf_π (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction (Gal(Ksep / K)) M]
    [ContinuousSMul (Gal(Ksep / K)) M]
    (U : (ContinuousModule.IsFiniteGaloisQuotient (Gal(Ksep / K)) M).FullSubcategory) :
    profiniteGaloisSheaf K Ksep M ⟶ (profiniteGaloisSystem K Ksep M).obj U :=
  limit.π (profiniteGaloisSystem K Ksep M) U

end AlgebraicGeometry.Scheme.ProEt

end
