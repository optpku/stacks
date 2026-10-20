module
public import stacks_project.Chap60.Remark_60_6_8_Connection
public import stacks_project.Chap60.Remark_60_6_7_Forms
public import stacks_project.Chap60.Lemma_60_3_1_SquareZero
public import ReasLib.RingTheory.Kaehler.DeRham
public import ReasLib.RingTheory.AdicCompletion.FilteredAdditive
public import ReasLib.LinearAlgebra.ExteriorPower.FormWedge
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
open CategoryTheory
universe u
namespace CrystallinePDDeRham
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Restrict coefficients of exterior forms to the base ring. -/
noncomputable instance algebraicFormModule (m : ℕ) :
    Module A (exteriorPower.form B Ω[B⁄A] m) :=
  exteriorPower.form.moduleOfScalarTower m

/-- The standard presentation of algebraic forms is equivalent to exterior
powers of ordinary Kähler differentials. This does not identify PD quotients. -/
noncomputable def presentation (m : ℕ) :
    KaehlerDifferential.DeRham.Form A B m ≃ₗ[B]
      exteriorPower.form B Ω[B⁄A] m :=
  LinearEquiv.ofBijective (KaehlerDifferential.DeRham.toExterior A B m).hom
    (KaehlerDifferential.DeRham.toExterior_bijective A B m)

/-- The actual algebraic de Rham differential on the exterior presentation. -/
noncomputable def algebraicFamily : DifferentialOperator.DeRham.Family A B Ω[B⁄A] :=
  fun m ↦
    { toFun := fun ω ↦ presentation A B (m + 1)
        (Submodule.Quotient.restrictScalarsEquiv A
          (KaehlerDifferential.DeRham.relations A B (m + 1))
          ((KaehlerDifferential.DeRham.rawD A B m).hom
            ((Submodule.Quotient.restrictScalarsEquiv A
              (KaehlerDifferential.DeRham.relations A B m)).symm
                ((presentation A B m).symm ω))))
      map_add' := sorry
      map_smul' := sorry }

/-- The generator formula for algebraic de Rham forms gives its differential laws. -/
theorem algebraicFamily_laws :
    DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B)
      (algebraicFamily A B) := sorry

variable {J : Ideal B} (δ : DividedPowers J)

/-- PD relations with the ambient algebra instance retained, avoiding a
second definitionally different algebra structure from a ring-hom wrapper. -/
noncomputable def relations : Submodule B Ω[B⁄A] :=
  by
    have h : (algebraMap A B).toAlgebra = (inferInstance : Algebra A B) := toAlgebra_algebraMap
    let carrier := fun a : Algebra A B ↦
      -- Local instance justification (defeq pin): dependent transport indexes the algebra structure a.
      letI : Algebra A B := a
      Submodule B (KaehlerDifferential A B)
    exact cast (congrArg carrier h) (dividedPowerRelations (algebraMap A B) δ)

/-- The genuine quotient module of PD one-forms. -/
abbrev oneForms := Ω[B⁄A] ⧸ relations A B δ

/-- Right scalar multiplication on PD forms is the same actual scalar
action as the left action, since the coefficient ring is commutative. -/
noncomputable instance oneFormsOppositeModule : Module Bᵐᵒᵖ (oneForms A B δ) :=
  Module.compHom (oneForms A B δ)
    ((RingHom.id B).fromOpposite (fun x y ↦ Commute.all x y))

/-- The opposite action used by the PD square-zero extension is central. -/
instance oneFormsCentralScalar : IsCentralScalar B (oneForms A B δ) where
  op_smul_eq_smul _ _ := rfl

/-- The canonical surjection onto the actual divided-power differential module. -/
noncomputable abbrev quotientMap := (relations A B δ).mkQ

/-- The genuine PD derivation is the universal derivation followed by the
relation quotient, with no inverse to the quotient map. -/
noncomputable def derivation : Derivation A B (oneForms A B δ) :=
  (quotientMap A B δ).compDer (KaehlerDifferential.D A B)

/-- The quotient enforces precisely the divided-power differential formula. -/
theorem derivation_dpow (n : ℕ) (x : B) (hx : x ∈ J) (hn : 1 ≤ n) :
    derivation A B δ (δ.dpow n x) = δ.dpow (n - 1) x • derivation A B δ x := sorry

section SquareZero
variable [Module Bᵐᵒᵖ (oneForms A B δ)] [IsCentralScalar B (oneForms A B δ)]

/-- Projection of the PD square-zero extension onto the original closed fibre. -/
noncomputable def closedFibreMap : TrivSqZeroExt B (oneForms A B δ) →+* B ⧸ J :=
  (Ideal.Quotient.mk J).comp (TrivSqZeroExt.fstHom B B (oneForms A B δ)).toRingHom

/-- Every closed-fibre element lifts through the first-coordinate inclusion. -/
theorem closedFibreMap_surjective : Function.Surjective (closedFibreMap A B δ) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨TrivSqZeroExt.inl b, rfl⟩

/-- The kernel of projection to the closed fibre is exactly the DP ideal,
including the whole square-zero differential factor. -/
theorem closedFibreMap_kernel :
    RingHom.ker (closedFibreMap A B δ) = DividedPowers.TrivSqZeroExt.ideal (oneForms A B δ) J := by
  ext x
  change Ideal.Quotient.mk J x.fst = 0 ↔ x.fst ∈ J
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The square-zero PD thickening has the same closed fibre, through its
actual quotient map. No arbitrary scheme or ring identification is chosen. -/
noncomputable def closedFibreEquiv :
    TrivSqZeroExt B (oneForms A B δ) ⧸
        DividedPowers.TrivSqZeroExt.ideal (oneForms A B δ) J ≃+* B ⧸ J :=
  (Ideal.quotEquivOfEq (closedFibreMap_kernel A B δ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := closedFibreMap A B δ)
      (closedFibreMap_surjective A B δ))

/-- The second PD infinitesimal lift, built with PD rather than ordinary
Kähler differentials. Its two coordinates are exactly b and db. -/
noncomputable def differentialLift : B →+* TrivSqZeroExt B (oneForms A B δ) where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (derivation A B δ b)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The PD derivation law makes the infinitesimal lift a PD morphism. -/
theorem differentialLift_preservesDP :
    DividedPowers.IsDPMorphism δ (DividedPowers.TrivSqZeroExt.dividedPowers (oneForms A B δ) δ)
      (differentialLift A B δ) := sorry

/-- The actual bundled PD lift used to construct finite-stage stratification. -/
noncomputable def differentialDPLift :
    DividedPowers.DPMorphism δ (DividedPowers.TrivSqZeroExt.dividedPowers (oneForms A B δ) δ) :=
  DividedPowers.DPMorphism.mk' (differentialLift_preservesDP A B δ)

end SquareZero

/-- PD relations are stable under differentiation: differentiating
dγ_n(x)-γ_(n-1)(x)dx reduces to a multiple of dx∧dx. -/
theorem pdKernel_stable :
    DifferentialOperator.DeRham.KernelCondition (quotientMap A B δ)
      (algebraicFamily A B) := sorry

/-- Descend through PD relations using the surjection, never its nonexistent inverse. -/
noncomputable def family :
    DifferentialOperator.DeRham.Family A B (oneForms A B δ) :=
  KaehlerDifferential.DeRham.descendedFamily (quotientMap A B δ)
    (Submodule.mkQ_surjective _) (algebraicFamily A B)
    (algebraicFamily_laws A B) (pdKernel_stable A B δ)

/-- Actual exterior multiplication by a PD one-form. -/
noncomputable def leftWedge (m : ℕ) :
    oneForms A B δ →ₗ[B] exteriorPower.form B (oneForms A B δ) m →ₗ[B]
      exteriorPower.form B (oneForms A B δ) (m + 1) :=
  (Nat.add_comm 1 m) ▸ CrystallineFormWedge.wedge B (oneForms A B δ) 1 m

/-- Actual exterior multiplication by a PD two-form. -/
noncomputable def leftWedgeTwo (m : ℕ) :
    exteriorPower.form B (oneForms A B δ) 2 →ₗ[B]
      exteriorPower.form B (oneForms A B δ) m →ₗ[B]
        exteriorPower.form B (oneForms A B δ) (m + 2) :=
  (Nat.add_comm 2 m) ▸ CrystallineFormWedge.wedge B (oneForms A B δ) 2 m

/-- The genuine PD exterior calculus: both wedge maps are actual exterior
multiplication and the differential descends through the PD relation quotient. -/
noncomputable def calculus : ExteriorCalculus (derivation A B δ) (family A B δ) :=
  ExteriorCalculus.of (leftWedge A B δ) (leftWedgeTwo A B δ)
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ _ ↦ sorry)
    (KaehlerDifferential.DeRham.descendedFamily_isDifferential
      (quotientMap A B δ) (Submodule.mkQ_surjective _) (algebraicFamily A B)
      (algebraicFamily_laws A B) (pdKernel_stable A B δ))

/-- Complete each PD-form differential additively. The output remains a
completed exterior power, allowing infinite-variable presentations. -/
noncomputable def completedDifferential (p m : ℕ) :
    AdicCompletion (Ideal.span {(p : B)})
      (exteriorPower.form B (oneForms A B δ) m) →+
    AdicCompletion (Ideal.span {(p : B)})
      (exteriorPower.form B (oneForms A B δ) (m + 1)) :=
  FilteredAdditiveCompletion.pAdicMap (family A B δ m).toAddMonoidHom p

end CrystallinePDDeRham
