/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.RelationParameter.TensorProduct
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w

/- 37.39.6.2: The universal relation and equation maps form the first part of the displayed
complex. -/
@[stacks 0CB0] #check
  (MvPolynomial.RelationParameter.equationMap_comp_relationMap :
    ∀ {C : Type u} [CommRing C] {n m K : ℕ}
      (f : Fin m → MvPolynomial (Fin n) C) (Ω : Finset (Fin n →₀ ℕ))
      (_ : ∀ j, (f j).support ⊆ Ω),
      (MvPolynomial.RelationParameter.equationMap C (K := K) f Ω).comp
        (MvPolynomial.RelationParameter.relationMap C (K := K) f Ω) = 0)

/- The equation map is exact with the tensor-product evaluation map, which is surjective. -/
#check
  (MvPolynomial.RelationParameter.exact_equationMap_evaluationMap :
    ∀ {C : Type u} {B : Type v} [CommRing C] [CommRing B] [Algebra C B]
      {n m K : ℕ} (x : Fin n → B) (f : Fin m → MvPolynomial (Fin n) C)
      (Ω : Finset (Fin n →₀ ℕ)) (_ : ∀ j, (f j).support ⊆ Ω)
      (_ : Function.Exact
        (Finsupp.linearCombination (MvPolynomial (Fin n) C) f)
        (MvPolynomial.aeval x : MvPolynomial (Fin n) C →ₐ[C] B))
      (_ : Function.Surjective
        (MvPolynomial.aeval x : MvPolynomial (Fin n) C →ₐ[C] B)),
      Function.Exact
          (MvPolynomial.RelationParameter.equationMap C (K := K) f Ω)
          (MvPolynomial.RelationParameter.evaluationMap (K := K) x f Ω) ∧
        Function.Surjective
          (MvPolynomial.RelationParameter.evaluationMap (K := K) x f Ω))

/- Coefficient specialization identifies the relation family, equations, and evaluation map. -/
#check
  (MvPolynomial.RelationParameter.maps_baseChange :
    ∀ {C : Type u} {B : Type v} {Rhat : Type w}
      [CommRing C] [CommRing B] [CommRing Rhat] [Algebra C B] [Algebra C Rhat]
      {n m K : ℕ} (x : Fin n → B) (f : Fin m → MvPolynomial (Fin n) C)
      (Ω : Finset (Fin n →₀ ℕ)) (a : Fin K → Fin m →₀ MvPolynomial (Fin n) Rhat)
      (_ : ∀ j, (f j).support ⊆ Ω) (_ : ∀ k j, (a k j).support ⊆ Ω)
      (tildeσ : MvPolynomial.RelationParameter.CoefficientAlgebra C K f Ω →ₐ[C] Rhat)
      (_ : ∀ k j (I : Ω),
        tildeσ ((algebraMap (MvPolynomial (Fin K × Fin m × Ω) C)
          (MvPolynomial.RelationParameter.CoefficientAlgebra C K f Ω))
            (MvPolynomial.X (k, j, I))) = MvPolynomial.coeff I.1 (a k j)),
      let mapCoefficients := MvPolynomial.map tildeσ.toRingHom
      ((fun k ↦ Finsupp.mapRange mapCoefficients mapCoefficients.map_zero
          (MvPolynomial.RelationParameter.vector C f Ω k)),
        (fun j ↦ mapCoefficients
          (MvPolynomial.map
            (algebraMap C (MvPolynomial.RelationParameter.CoefficientAlgebra C K f Ω))
            (f j))),
        (Algebra.TensorProduct.map (AlgHom.id C B) tildeσ).toRingHom.comp
          (MvPolynomial.RelationParameter.evaluationMap (K := K) x f Ω)) =
        (a, (fun j ↦ MvPolynomial.map (algebraMap C Rhat) (f j)),
          (MvPolynomial.eval₂Hom
            (Algebra.TensorProduct.includeRight : Rhat →ₐ[C] B ⊗[C] Rhat).toRingHom
            (fun i ↦ (Algebra.TensorProduct.includeLeft : B →ₐ[C] B ⊗[C] Rhat) (x i))).comp
              mapCoefficients))
