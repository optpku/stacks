/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.FiniteGaloisFiber
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.GaloisComparison
public import ReasLib.CategoryTheory.Action.Finite.Discrete

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- A supplied separable closure embeds in the canonical algebraic closure. -/
def finiteGaloisClosureEmbedding : Ksep →ₐ[K] AlgebraicClosure K := IsSepClosed.lift

section Embedded

variable [Algebra Ksep (AlgebraicClosure K)]
  [IsScalarTower K Ksep (AlgebraicClosure K)]

/-- Extension and geometric-fiber action identify the two topological Galois groups. -/
def finiteGaloisFiberGroupEquiv :
    Gal(Ksep/K) ≃ₜ* Aut (specFieldGeometricPoint K (AlgebraicClosure K)).finiteFiber where
  toMulEquiv := (AlgEquiv.sepClosureEquivAlgClosure K (AlgebraicClosure K) Ksep).trans
    (galoisAlgClosureEquivFundamentalGroup K)
  continuous_toFun := sorry
  continuous_invFun := sorry

/-- The native finite Galois classification, transported along the actual group isomorphism. -/
def finiteGaloisClassification :
    Scheme.FiniteEtale (Spec (.of K)) ≌ DiscreteContAction FintypeCat.{u} Gal(Ksep/K) :=
  ((functorToContAction
      (specFieldGeometricPoint K (AlgebraicClosure K)).finiteFiber).asEquivalence.trans
    (ContAction.resEquiv FintypeCat (finiteGaloisFiberGroupEquiv K Ksep))).trans
      (ContAction.finiteDiscreteEquivalence Gal(Ksep/K))

/-- Scalar extension and affine coordinate descent identify the classified action with
the prescribed separable-closure-valued point action. -/
def finiteGaloisClassificationIso :
    (finiteGaloisClassification K Ksep).functor ≅ finiteEtaleGaloisFiber K Ksep :=
  NatIso.ofComponents
    (fun Y ↦ ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
      Action.mkIso
        (FintypeCat.equivEquivIso
          (finiteEtaleSepFiber_equivGeometric K (AlgebraicClosure K) Ksep Y).symm)
        (fun _ ↦ sorry))
    (fun _ ↦ sorry)

/-- The classification equivalence with exactly the prescribed point-action functor. -/
def finiteEtaleGaloisEquivalenceOfEmbedding :
    Scheme.FiniteEtale (Spec (.of K)) ≌ DiscreteContAction FintypeCat.{u} Gal(Ksep/K) :=
  (finiteGaloisClassification K Ksep).changeFunctor (finiteGaloisClassificationIso K Ksep)

end Embedded

/-- Finite étale schemes over a field are classified by finite continuous actions on
points valued in any specified separable closure. -/
def finiteEtaleGaloisEquivalence :
    Scheme.FiniteEtale (Spec (.of K)) ≌ DiscreteContAction FintypeCat.{u} Gal(Ksep/K) := by
  let embedding := finiteGaloisClosureEmbedding K Ksep
  letI : Algebra Ksep (AlgebraicClosure K) := embedding.toRingHom.toAlgebra
  letI : IsScalarTower K Ksep (AlgebraicClosure K) := IsScalarTower.of_algHom embedding
  exact finiteEtaleGaloisEquivalenceOfEmbedding K Ksep

/-- The forward functor is the original separable point-fiber functor. -/
theorem finiteEtaleGaloisEquivalence_functor :
    (finiteEtaleGaloisEquivalence K Ksep).functor = finiteEtaleGaloisFiber K Ksep := rfl

/-- The original classification certificate is supplied by the constructed equivalence. -/
instance finiteEtaleGaloisFiber_isEquivalence :
    (finiteEtaleGaloisFiber K Ksep).IsEquivalence :=
  (finiteEtaleGaloisEquivalence K Ksep).isEquivalence_functor

end AlgebraicGeometry.Scheme.Etale

end
