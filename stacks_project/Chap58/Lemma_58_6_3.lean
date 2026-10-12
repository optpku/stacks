/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap58.Lemma_58_6_3_GaloisFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale
open scoped FintypeCatDiscrete

universe u

variable (K Kbar Ksep : Type u)
variable [Field K] [Field Kbar] [Field Ksep]
variable [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
variable [IsScalarTower K Ksep Kbar]
variable [IsAlgClosed Kbar] [IsSepClosure K Ksep]

/- Lemma 58.6.3 (1): finite étale schemes over `Spec K` are equivalent to finite
discrete continuous `Gal(Ksep/K)`-sets. -/
@[stacks 0BNE] #check (AlgebraicGeometry.Scheme.Etale.finiteEtaleGaloisFiber_isEquivalence K Ksep :
  (finiteEtaleGaloisFiber K Ksep).IsEquivalence)

#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleGaloisFiber_comp_forget_iso K Kbar Ksep :
  finiteEtaleGaloisFiber K Ksep ⋙
    (forget₂ (DiscreteContAction FintypeCat Gal(Ksep/K)) (ContAction FintypeCat Gal(Ksep/K)) ⋙
      forget₂ (ContAction FintypeCat Gal(Ksep/K)) FintypeCat) ≅
    (specFieldGeometricPoint K Kbar).finiteFiber)

/- Lemma 58.6.3 (2): the canonical comparison `Gal(Ksep/K) → π₁(Spec K, xbar)` is an
isomorphism of profinite topological groups. -/
@[stacks 0BNE] #check (AlgebraicGeometry.Scheme.Etale.galoisToFundamentalGroup_isHomeomorph
  K Kbar Ksep : IsHomeomorph (galoisToFundamentalGroup K Kbar Ksep))
