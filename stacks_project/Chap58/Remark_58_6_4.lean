/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap58.Remark_58_6_4_GaloisAction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.GeometricPoint

universe u

noncomputable section

/- Remark 58.6.4 (1): in the situation of Lemma 58.6.3, `Gal(Ksep/K) ≃* Gal(Kbar/K)` by
unique extension from the separable closure to the algebraic closure. -/
@[stacks 0BQ9] #check (AlgEquiv.sepClosureEquivAlgClosure :
  ∀ (K Kbar Ksep : Type u) [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosure K Kbar] [IsSepClosure K Ksep],
    Gal(Ksep/K) ≃* Gal(Kbar/K))

/- Remark 58.6.4 (2): an automorphism acts on a geometric fiber by precomposition with the
corresponding morphism of spectra. -/
@[stacks 0BQ9] #check (AlgebraicGeometry.Scheme.Etale.galoisAlgClosure_smul_apply :
  ∀ {K Kbar : Type u} [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y : Scheme.FiniteEtale (Spec (.of K))} (σ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y),
    (galoisAlgClosure_smul σ ybar).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ ybar.left)

/- Remark 58.6.4 (3): the action satisfies `(σ * τ) • ybar = σ • (τ • ybar)`. -/
@[stacks 0BQ9] #check (AlgebraicGeometry.Scheme.Etale.galoisAlgClosure_mul_smul :
  ∀ {K Kbar : Type u} [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y : Scheme.FiniteEtale (Spec (.of K))} (σ τ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y),
    galoisAlgClosure_smul (σ * τ) ybar =
      galoisAlgClosure_smul σ (galoisAlgClosure_smul τ ybar))

/- Remark 58.6.4 (4): the action is functorial in the finite étale scheme. -/
@[stacks 0BQ9] #check (AlgebraicGeometry.Scheme.Etale.galoisAlgClosure_smul_map :
  ∀ {K Kbar : Type u} [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y Z : Scheme.FiniteEtale (Spec (.of K))} (f : Y ⟶ Z) (σ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y),
    ((specFieldGeometricPoint K Kbar).finiteFiber).map f (galoisAlgClosure_smul σ ybar) =
      galoisAlgClosure_smul σ (((specFieldGeometricPoint K Kbar).finiteFiber).map f ybar))

/- Remark 58.6.4 (5): the action induces the homomorphism `Aut(Kbar/K) → Aut(F_xbar)`. -/
@[stacks 0BQ9] #check (AlgebraicGeometry.Scheme.Etale.galoisAlgClosureToFundamentalGroup :
  ∀ (K Kbar : Type u) [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar],
    Gal(Kbar/K) →* Aut ((specFieldGeometricPoint K Kbar).finiteFiber))

/- Remark 58.6.4 (6): after transporting along the closure equivalence, the induced
homomorphism agrees with the canonical separable-closure comparison. -/
@[stacks 0BQ9] #check
  (AlgebraicGeometry.Scheme.Etale.galoisAlgClosureToFundamentalGroup_comp_restrict :
    ∀ (K Kbar Ksep : Type u) [Field K] [Field Kbar] [Field Ksep]
      [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
      [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsAlgClosure K Kbar]
      [IsSepClosure K Ksep],
      (galoisAlgClosureToFundamentalGroup K Kbar).comp
          (AlgEquiv.sepClosureEquivAlgClosure K Kbar Ksep).toMonoidHom =
        (galoisToFundamentalGroup K Kbar Ksep).toMonoidHom)

end
