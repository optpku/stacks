/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Galois.Cohomology.Units
public import ReasLib.Algebra.CentralSimple.GaloisDescent
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group

@[expose] public section

universe u v

open scoped MatrixGroups

namespace BrauerGroup

variable (K : Type u) (Ksep : Type v) [Field K] [Field Ksep]
variable [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The continuous scalar-boundary class obtained by splitting a central simple algebra
over a separable closure and taking its matrix descent. -/
noncomputable def representativeDelta (A : CSA.{u, max u v} K) :
    Multiplicative (GaloisCohomology.h2Units K Ksep) :=
  let size := A.separableSplittingSize
  let splitting := A.separableSplittingEquiv Ksep
  Multiplicative.ofAdd (GaloisCohomology.twoCocycleClass K Ksep
    ⟨CSA.descentBoundary Ksep A size splitting,
      CSA.descentBoundary_locallyConstant Ksep A size splitting⟩
    (brauerTwoCocycle_isMulCocycle₂ K size size.pos
      (CSA.descentCocycle Ksep A size splitting) (CSA.descentLift Ksep A size splitting)
      (CSA.descentCocycle_cocycle Ksep A size splitting) (fun _ ↦ rfl)))

/-- The scalar-boundary class of an algebra can be computed from any positive-size splitting. -/
theorem representativeDelta_eq_of_split (A : CSA.{u, max u v} K) (n : ℕ+)
    (e : A.baseChange Ksep ≃ₐ[Ksep] Matrix (Fin n) (Fin n) Ksep) :
    representativeDelta K Ksep A = Multiplicative.ofAdd
      (GaloisCohomology.twoCocycleClass K Ksep
        ⟨CSA.descentBoundary Ksep A n e, CSA.descentBoundary_locallyConstant Ksep A n e⟩
        (brauerTwoCocycle_isMulCocycle₂ K n n.pos
          (CSA.descentCocycle Ksep A n e) (CSA.descentLift Ksep A n e)
          (CSA.descentCocycle_cocycle Ksep A n e) (fun _ ↦ rfl))) := sorry

/-- Brauer-equivalent central simple algebras define the same scalar-boundary class. -/
theorem representativeDelta_eq_of_brauerEquivalent (A B : CSA.{u, max u v} K)
    (hAB : IsBrauerEquivalent A B) :
    representativeDelta K Ksep A = representativeDelta K Ksep B := sorry

/-- The neutral central simple algebra has trivial scalar-boundary class. -/
theorem representativeDelta_one :
    representativeDelta K Ksep (CSA.unit K) = 1 := sorry

/-- Tensor product of central simple algebras multiplies their scalar-boundary classes. -/
theorem representativeDelta_tensorProduct (A B : CSA.{u, max u v} K) :
    representativeDelta K Ksep (A.tensorProduct B) =
      representativeDelta K Ksep A * representativeDelta K Ksep B := sorry

/-- The Brauer connecting homomorphism sends an algebra class to its continuous Galois
scalar-boundary class. -/
noncomputable def delta : Br.{u, v} K →* Multiplicative (GaloisCohomology.h2Units K Ksep) where
  toFun := Quotient.lift (representativeDelta K Ksep)
    (representativeDelta_eq_of_brauerEquivalent K Ksep)
  map_one' := representativeDelta_one K Ksep
  map_mul' := fun first second ↦ Quotient.inductionOn₂ first second
    (representativeDelta_tensorProduct K Ksep)

/-- Evaluation of the Brauer connecting homomorphism is the continuous scalar-boundary
class computed from any matrix splitting of the representative. -/
theorem delta_spec (A : CSA.{u, max u v} K) (n : ℕ+)
    (e : A.baseChange Ksep ≃ₐ[Ksep] Matrix (Fin n) (Fin n) Ksep) :
    delta K Ksep (Quotient.mk _ A) = Multiplicative.ofAdd
      (GaloisCohomology.twoCocycleClass K Ksep
        ⟨CSA.descentBoundary Ksep A n e, CSA.descentBoundary_locallyConstant Ksep A n e⟩
        (brauerTwoCocycle_isMulCocycle₂ K n n.pos
          (CSA.descentCocycle Ksep A n e) (CSA.descentLift Ksep A n e)
          (CSA.descentCocycle_cocycle Ksep A n e) (fun _ ↦ rfl))) := sorry

/-- The Brauer connecting homomorphism to continuous second Galois cohomology of units is bijective. -/
theorem delta_isomorphism : Function.Bijective (delta K Ksep) := sorry

/-- The multiplicative equivalence whose forward map is the Brauer connecting homomorphism. -/
noncomputable def deltaEquiv : Br.{u, v} K ≃* Multiplicative (GaloisCohomology.h2Units K Ksep) :=
  MulEquiv.ofBijective (delta K Ksep) (delta_isomorphism K Ksep)

/-- The Brauer equivalence evaluates as the connecting homomorphism. -/
theorem deltaEquiv_apply (brauerClass : Br.{u, v} K) :
    deltaEquiv K Ksep brauerClass = delta K Ksep brauerClass := sorry

end BrauerGroup

end
