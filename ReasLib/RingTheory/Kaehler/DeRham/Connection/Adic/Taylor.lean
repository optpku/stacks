/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic.BaseChange
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

noncomputable section

set_option backward.privateInPublic true

open CategoryTheory DPPolynomial.DeRham DividedPowerEnvelope
open scoped TensorProduct Classical

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
variable (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E')

variable [Algebra.Smooth A P']
variable (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')

namespace Connection.Adic

/-- Nilpotence of the prime in the quotient of a crystalline envelope. -/
private def quotientNilpotent : IsNilpotent (p : E'.D ⧸ E'.D.ideal) :=
  let bound := DividedPowers.PAdic.pAdicCompletionIsCrisWedgeObject p A P' I γ C
    (algebraMap A C) π'.toRingHom π'.comp_algebraMap hIC J' hJ' hπ' hpnil E' hE'
  ⟨bound.choose,
    (map_pow (Ideal.Quotient.mk E'.D.ideal) (p : E'.D) bound.choose).symm.trans
      ((Ideal.Quotient.eq_zero_iff_mem).mpr
        (bound.choose_spec.2.choose
          (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : E'.D))) bound.choose)))⟩

variable {p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'}


/-- The coordinate endomorphism determined by a polynomial completed-envelope retract. -/
private abbrev sigma := R.b.comp R.a

/-- The original polynomial-envelope algebra action relative to the coefficient ring. -/
private abbrev polynomialBase := Coordinates.baseAlgebra R.E

variable (M : ModuleCat.{u} R.polyD)
variable (conn :
  -- Local instance justification (noncanonical choice): the polynomial connection uses its envelope's structural coefficient map.
  letI := polynomialBase R
  Adic A R.E.D R.E.D.dividedPowers p M)
variable (hcomplete : IsAdicComplete (Ideal.span {(p : R.polyD)}) M)

/-- Ordered iteration of polynomial coordinate differential operators for a multi-index. -/
private def taylorDerivative (k : Fin R.n → ℕ) (m : M) : M :=
  -- Local instance justification (noncanonical choice): coordinate operators use the specified polynomial-envelope connection.
  letI := Coordinates.baseAlgebra R.E
  (List.finRange R.n).foldl
    (fun v i ↦ («partial» conn hcomplete (Coordinates.completedCoord R.E R.hE p ⟨i⟩))^[k i] v) m

/-- The difference of a polynomial coordinate and its image under the retract endomorphism. -/
private def taylorDifference (i : Fin R.n) : R.polyD :=
  let x := algebraMap R.E.D R.polyD (R.E.toD (MvPolynomial.X (ULift.up i)))
  x - R.b (R.a x)

/-- The finite divided-power Taylor sum into the twisted scalar tensor. -/
private def taylorForwardSum (bound : ℕ) (m : M) :
    scalarExtensionTensor (sigma R) M :=
  let σ := sigma R
  let unit := ((ModuleCat.extendRestrictScalarsAdj σ).unit.app M).hom
  ∑ k : Fin R.n → Fin bound,
    (∏ i : Fin R.n, R.γbar.dpow (k i).val (taylorDifference R i)) •
      unit (taylorDerivative R M conn hcomplete
        (fun i ↦ (k i).val) m)

/-- The finite reverse Taylor sum uses the opposite coordinate differences. -/
private def taylorReverseSum (bound : ℕ) (m : M) : M :=
  ∑ k : Fin R.n → Fin bound,
    (∏ i : Fin R.n, R.γbar.dpow (k i).val (-taylorDifference R i)) •
      taylorDerivative R M conn hcomplete
        (fun i ↦ (k i).val) m

variable (hintegrable :
  -- Local instance justification (noncanonical choice): intrinsic integrability is relative to the polynomial envelope coefficient map.
  letI := Coordinates.baseAlgebra R.E
  IsIntegrable A R.E.D R.E.D.dividedPowers p conn)
variable (hqn :
  -- Local instance justification (noncanonical choice): coordinatewise quasi-nilpotence uses the polynomial envelope coefficient map.
  letI := Coordinates.baseAlgebra R.E
  IsTopologicallyQuasiNilpotent conn hcomplete (Coordinates.completedCoord R.E R.hE p))

include hintegrable hqn in
/-- Divided-power Taylor sums stabilize in every finite principal-adic quotient. -/
theorem taylorBound_exists (degree : ℕ) (m : M) :
    ∃ bound : ℕ, ∀ b ≥ bound,
      Submodule.Quotient.mk
          (p := (Ideal.span {(p : R.polyD)} ^ degree • ⊤ :
            Submodule R.polyD (scalarExtensionTensor (sigma R) M)))
          (taylorForwardSum R M conn hcomplete b m) =
        Submodule.Quotient.mk
          (taylorForwardSum R M conn hcomplete bound m) ∧
      Submodule.Quotient.mk
          (p := (Ideal.span {(p : R.polyD)} ^ degree • ⊤ : Submodule R.polyD M))
          (taylorReverseSum R M conn hcomplete b m) =
        Submodule.Quotient.mk
          (taylorReverseSum R M conn hcomplete bound m) := sorry

/-- The least finite truncation bound for a Taylor sum in a specified quotient. -/
private def taylorBound (degree : ℕ) (m : M) : ℕ :=
  Nat.find (taylorBound_exists R M conn hcomplete hintegrable hqn degree m)

/-- The stabilized forward Taylor value in a finite coefficient quotient. -/
private def taylorForwardStage (degree : ℕ) (m : M) :=
  Submodule.Quotient.mk
    (p := (Ideal.span {(p : R.polyD)} ^ degree • ⊤ :
      Submodule R.polyD (scalarExtensionTensor (sigma R) M)))
    (taylorForwardSum R M conn hcomplete
      (taylorBound R M conn hcomplete hintegrable hqn degree m) m)

/-- The stabilized reverse Taylor value in a finite coefficient quotient. -/
private def taylorReverseStage (degree : ℕ) (m : M) :=
  Submodule.Quotient.mk
    (p := (Ideal.span {(p : R.polyD)} ^ degree • ⊤ : Submodule R.polyD M))
    (taylorReverseSum R M conn hcomplete
      (taylorBound R M conn hcomplete hintegrable hqn degree m) m)

/-- Finite Taylor values are compatible, additive, and satisfy the two scalar-balancing identities. -/
theorem taylorStage_laws :
    let σ := sigma R
    let V := scalarExtensionTensor σ M
    let forward := taylorForwardStage R M conn hcomplete hintegrable hqn
    let reverse := taylorReverseStage R M conn hcomplete hintegrable hqn
    (∀ m {i j} (h : i ≤ j), AdicCompletion.transitionMap (Ideal.span {(p : R.polyD)}) V h (forward j m) = forward i m) ∧
    (∀ m {i j} (h : i ≤ j), AdicCompletion.transitionMap (Ideal.span {(p : R.polyD)}) M h (reverse j m) = reverse i m) ∧
    (∀ d, forward d 0 = 0) ∧ (∀ d m n, forward d (m + n) = forward d m + forward d n) ∧
    (∀ d (r : R.polyD) m, forward d (r • m) = r • forward d m) ∧
    (∀ d, reverse d 0 = 0) ∧ (∀ d m n, reverse d (m + n) = reverse d m + reverse d n) ∧
    (∀ d (r : R.polyD) m, reverse d (r • m) = σ r • reverse d m) := sorry

/-- The convergent forward Taylor map on the original complete coefficient module. -/
def taylorComparison : M →ₗ[R.polyD]
    completedScalarExtension (sigma R) p M :=
  let laws := taylorStage_laws R M conn hcomplete hintegrable hqn
  let stage := taylorForwardStage R M conn hcomplete hintegrable hqn
  AdicCompletion.lift (Ideal.span {(p : R.polyD)})
    (fun d ↦ { toFun := stage d, map_add' := laws.2.2.2.1 d, map_smul' := laws.2.2.2.2.1 d })
    (fun h ↦ LinearMap.ext (fun m ↦ laws.1 m h))

/-- The reverse Taylor series as a semilinear map into the completed original module. -/
private def reverseSeries : M →ₛₗ[sigma R]
    AdicCompletion (Ideal.span {(p : R.polyD)}) M :=
  let laws := taylorStage_laws R M conn hcomplete hintegrable hqn
  let stage := taylorReverseStage R M conn hcomplete hintegrable hqn
  { toFun := fun m ↦ ⟨fun d ↦ stage d m, laws.2.1 m⟩
    map_add' := fun m n ↦ Subtype.ext (funext (fun d ↦ laws.2.2.2.2.2.2.1 d m n))
    map_smul' := fun r m ↦ Subtype.ext (funext (fun d ↦ laws.2.2.2.2.2.2.2 d r m)) }

/-- Reverse Taylor descent through the twisted scalar tensor. -/
private def reverseTensor :
    scalarExtensionTensor (sigma R) M →ₗ[R.polyD] M :=
  let σ := sigma R
  let series := reverseSeries R M conn hcomplete hintegrable hqn
  let completionInverse :=
    (LinearEquiv.ofBijective (AdicCompletion.of (Ideal.span {(p : R.polyD)}) M)
      (AdicCompletion.of_bijective_iff.mpr hcomplete)).symm.toLinearMap
  let restricted : M ⟶ (ModuleCat.restrictScalars σ).obj (ModuleCat.of R.polyD M) :=
    ConcreteCategory.ofHom (C := ModuleCat R.polyD) (X := M)
      (Y := (ModuleCat.restrictScalars σ).obj (ModuleCat.of R.polyD M))
      ({ toFun := fun m ↦ completionInverse (series m)
         map_add' := fun m n ↦ (congrArg completionInverse (series.map_add m n)).trans (completionInverse.map_add _ _)
         map_smul' := fun r m ↦ (congrArg completionInverse (series.map_smulₛₗ r m)).trans (completionInverse.map_smul _ _) } :
        M →ₗ[R.polyD] (ModuleCat.restrictScalars σ).obj (ModuleCat.of R.polyD M))
  (((ModuleCat.extendRestrictScalarsAdj σ).homEquiv M (ModuleCat.of R.polyD M)).symm restricted).hom

/-- The inverse Taylor map is the continuous extension of the reverse-sign Taylor tensor formula. -/
def taylorComparisonInv :
    completedScalarExtension (sigma R) p M →ₗ[R.polyD] M :=
  let completionInverse :=
    (LinearEquiv.ofBijective (AdicCompletion.of (Ideal.span {(p : R.polyD)}) M)
      (AdicCompletion.of_bijective_iff.mpr hcomplete)).symm.toLinearMap
  completionInverse.comp
    ((AdicCompletion.map (Ideal.span {(p : R.polyD)})
      (reverseTensor R M conn hcomplete hintegrable hqn)).restrictScalars R.polyD)

/-- The connection obtained by actual completed scalar extension along the polynomial retract endomorphism. -/
private def taylorTargetConnection :
    -- Local instance justification (noncanonical choice): the target connection uses the polynomial envelope's coefficient action.
    letI := Coordinates.baseAlgebra R.E
    Adic A R.E.D R.E.D.dividedPowers p (completedScalarExtension (R.b.comp R.a) p M) :=
  let f := R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A))
  let hnil := quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
  Connection.Adic.baseChange f f R.E.D.dividedPowers R.E.D.dividedPowers p hnil hnil
    R.γbar R.γbar R.γbar_extends R.γbar_extends (R.b.comp R.a)
    ((congrArg (RingHom.comp R.b) R.a_base).trans R.b_base)
    (DividedPowers.IsDPMorphism.comp R.γbar R.b_isDP R.a_isDP) M conn

/-- Convergent divided-power Taylor maps in both directions commute with their genuine induced connections. -/
theorem taylorComparison_horizontal :
    -- Local instance justification (noncanonical choice): horizontality uses the polynomial envelope's specified coefficient action.
    letI := Coordinates.baseAlgebra R.E
    let forward := taylorComparison R M conn hcomplete hintegrable hqn
    let reverse := taylorComparisonInv R M conn hcomplete hintegrable hqn
    let target := taylorTargetConnection R M conn
    (∀ m, target.toAddMonoidHom (forward m) = tensorMap forward (conn.toAddMonoidHom m)) ∧
    (∀ m, conn.toAddMonoidHom (reverse m) = tensorMap reverse (target.toAddMonoidHom m)) := sorry

/-- The two convergent Taylor formulas are mutually inverse on complete quasi-nilpotent coefficients. -/
theorem taylorComparison_inverse :
    Function.LeftInverse (taylorComparisonInv R M conn hcomplete hintegrable hqn) (taylorComparison R M conn hcomplete hintegrable hqn) ∧
    Function.RightInverse (taylorComparisonInv R M conn hcomplete hintegrable hqn) (taylorComparison R M conn hcomplete hintegrable hqn) := sorry

variable {N : ModuleCat.{u} R.polyD}
variable (connN :
  -- Local instance justification (noncanonical choice): the second polynomial connection uses its envelope's structural coefficient action.
  letI := Coordinates.baseAlgebra R.E
  Adic A R.E.D R.E.D.dividedPowers p N)
variable (hcompleteN : IsAdicComplete (Ideal.span {(p : R.polyD)}) N)
variable (hintegrableN :
  -- Local instance justification (noncanonical choice): intrinsic integrability uses the polynomial envelope's structural action.
  letI := Coordinates.baseAlgebra R.E
  IsIntegrable A R.E.D R.E.D.dividedPowers p connN)
variable (hqnN :
  -- Local instance justification (noncanonical choice): polynomial coordinate operators use the envelope's structural action.
  letI := Coordinates.baseAlgebra R.E
  IsTopologicallyQuasiNilpotent connN hcompleteN (Coordinates.completedCoord R.E R.hE p))

/-- Convergent divided-power Taylor comparison is natural in horizontal coefficient homomorphisms. -/
theorem taylorComparison_natural
    (g :
      -- Local instance justification (noncanonical choice): horizontal maps use the polynomial envelope's structural coefficient action.
      letI := Coordinates.baseAlgebra R.E
      Hom conn connN) :
    -- Local instance justification (noncanonical choice): projecting the horizontal coefficient map uses the polynomial envelope's structural action.
    letI := Coordinates.baseAlgebra R.E
    (taylorComparison R N connN hcompleteN hintegrableN hqnN).comp g.toLinearMap =
      ((completedScalarExtensionMap (R.b.comp R.a) p (ModuleCat.ofHom g.toLinearMap)).hom).comp
        (taylorComparison R M conn hcomplete hintegrable hqn) := sorry

end Connection.Adic
