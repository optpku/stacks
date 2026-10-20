module

public import ReasLib.RingTheory.DividedPowers.Inseparable
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic
public import ReasLib.RingTheory.Localization.AtPrime.Int
public import Mathlib.Algebra.Homology.Homotopy

public section

open CategoryTheory
open DPPolynomial.DeRham
open exteriorPower.form
open scoped TensorProduct

universe u

namespace Connection.Adic

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
variable (lam : completedRingB B p)

/-- The divided-power differentiation relations transported from the base ring, together
with the differentiation relations of the formal divided powers of the new coordinate. -/
noncomputable def inseparableRelations :
    Submodule (DividedPowers.Inseparable.completion p lam)
      Ω[DividedPowers.Inseparable.completion p lam ⁄ A] :=
  Submodule.span _
    ({ω | ∃ (n : ℕ) (x : B), x ∈ J ∧ 1 ≤ n ∧
      ω = KaehlerDifferential.D A (DividedPowers.Inseparable.completion p lam) (algebraMap B (DividedPowers.Inseparable.completion p lam) (δ.dpow n x)) -
        algebraMap B (DividedPowers.Inseparable.completion p lam) (δ.dpow (n - 1) x) •
          KaehlerDifferential.D A (DividedPowers.Inseparable.completion p lam) (algebraMap B (DividedPowers.Inseparable.completion p lam) x)} ∪
    {ω | ∃ n : ℕ,
      ω = KaehlerDifferential.D A (DividedPowers.Inseparable.completion p lam) (DividedPowers.Inseparable.xiPow p lam (n + 1)) -
        DividedPowers.Inseparable.xiPow p lam n •
          KaehlerDifferential.D A (DividedPowers.Inseparable.completion p lam) (DividedPowers.Inseparable.xiPow p lam 1)})

/-- One-forms on the completed inseparable extension modulo divided-power differentiation. -/
noncomputable def inseparableOneForm : Type u :=
  Ω[DividedPowers.Inseparable.completion p lam ⁄ A] ⧸
    inseparableRelations A B δ p lam

/-- The quotient of Kähler one-forms carries its canonical additive group. -/
noncomputable instance inseparableOneFormAddCommGroup :
    AddCommGroup (inseparableOneForm A B δ p lam) :=
  inferInstanceAs (AddCommGroup (Ω[DividedPowers.Inseparable.completion p lam ⁄ A] ⧸
    inseparableRelations A B δ p lam))

/-- The extension ring acts on its quotient module of one-forms. -/
noncomputable instance inseparableOneFormExtensionModule :
    Module (DividedPowers.Inseparable.completion p lam)
      (inseparableOneForm A B δ p lam) :=
  inferInstanceAs (Module (DividedPowers.Inseparable.completion p lam)
    (Ω[DividedPowers.Inseparable.completion p lam ⁄ A] ⧸
      inseparableRelations A B δ p lam))

/-- Base coefficients act on the quotient one-forms through the canonical coefficient map. -/
noncomputable instance inseparableOneFormModule :
    Module B (inseparableOneForm A B δ p lam) :=
  Module.compHom _ (algebraMap B (DividedPowers.Inseparable.completion p lam))

/-- The base and extension scalar actions on quotient one-forms are compatible. -/
instance inseparableOneFormTower :
    IsScalarTower B (DividedPowers.Inseparable.completion p lam)
      (inseparableOneForm A B δ p lam) :=
  IsScalarTower.of_compHom B (DividedPowers.Inseparable.completion p lam)
    (inseparableOneForm A B δ p lam)

/-- The ground ring acts on the quotient one-forms through the extension ring. -/
noncomputable instance inseparableOneFormGroundModule :
    Module A (inseparableOneForm A B δ p lam) :=
  Module.compHom _ (algebraMap A (DividedPowers.Inseparable.completion p lam))

/-- Ground-ring scalars are compatible with extension scalars on quotient one-forms. -/
instance inseparableOneFormGroundTower :
    IsScalarTower A (DividedPowers.Inseparable.completion p lam)
      (inseparableOneForm A B δ p lam) :=
  IsScalarTower.of_compHom A (DividedPowers.Inseparable.completion p lam)
    (inseparableOneForm A B δ p lam)

/-- The ground-ring and base-ring scalar actions agree on the completed extension. -/
instance inseparableBaseTower :
    IsScalarTower A B (DividedPowers.Inseparable.completion p lam) :=
  ⟨fun a b r ↦ by
    ext n
    exact smul_assoc a b (r.val n)⟩

/-- Restriction to the base ring preserves the ground-ring action on quotient one-forms. -/
instance inseparableOneFormBaseTower :
    IsScalarTower A B (inseparableOneForm A B δ p lam) :=
  ⟨fun a b w ↦ by
    change (algebraMap B (DividedPowers.Inseparable.completion p lam) (a • b)) • w = _
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B
      (DividedPowers.Inseparable.completion p lam)]
    exact mul_smul _ _ _⟩

/-- The quotient of the universal Kähler derivation by the divided-power relations. -/
noncomputable def inseparableDerivation :
    Derivation A (DividedPowers.Inseparable.completion p lam)
      (inseparableOneForm A B δ p lam) :=
  (show Ω[DividedPowers.Inseparable.completion p lam ⁄ A] →ₗ[DividedPowers.Inseparable.completion p lam]
    inseparableOneForm A B δ p lam from
      (inseparableRelations A B δ p lam).mkQ).compDer
        (KaehlerDifferential.D A (DividedPowers.Inseparable.completion p lam))

/-- The Kähler coefficient map followed by the quotient by the target relations. -/
private noncomputable def inseparableKaehlerMap :
    Ω[B⁄A] →ₗ[B] inseparableOneForm A B δ p lam :=
  Derivation.liftKaehlerDifferential
    ((inseparableDerivation A B δ p lam).compAlgebraMap B)

/-- The transported base divided-power differentiation relations vanish in the target quotient. -/
theorem inseparableRelations_compatible :
    relationsB A B δ ≤ LinearMap.ker (Derivation.liftKaehlerDifferential
                  ((inseparableDerivation A B δ p lam).compAlgebraMap B) :
                    Ω[B⁄A] →ₗ[B] inseparableOneForm A B δ p lam) := sorry

/-- The coefficient map on uncompleted divided-power one-forms. -/
private noncomputable def inseparableOneFormMap :
    formB A B δ →ₗ[B] inseparableOneForm A B δ p lam :=
  (relationsB A B δ).liftQ (inseparableKaehlerMap A B δ p lam)
    (inseparableRelations_compatible A B δ p lam)

/-- Target forms have the completed extension ring in degree zero and completed exterior
powers of the quotient one-forms in positive degrees. -/
@[expose]
noncomputable def inseparableForm : ℕ → Type u
  | 0 => DividedPowers.Inseparable.completion p lam
  | degree + 1 => AdicCompletion (principalIdealB B p)
      (exteriorPower.form (DividedPowers.Inseparable.completion p lam)
        (inseparableOneForm A B δ p lam) (degree + 1))

/-- Each target form degree is an additive commutative group. -/
noncomputable instance inseparableFormAddCommGroup (degree : ℕ) :
    AddCommGroup (inseparableForm A B δ p lam degree) :=
  match degree with
  | 0 => inferInstanceAs (AddCommGroup (DividedPowers.Inseparable.completion p lam))
  | degree + 1 => inferInstanceAs (AddCommGroup (AdicCompletion (principalIdealB B p)
      (exteriorPower.form (DividedPowers.Inseparable.completion p lam)
        (inseparableOneForm A B δ p lam) (degree + 1))))

/-- The completed base ring acts canonically on every degree of the target forms. -/
noncomputable instance inseparableFormModule (degree : ℕ) :
    Module (completedRingB B p) (inseparableForm A B δ p lam degree) :=
  match degree with
  | 0 => inferInstanceAs (Module (completedRingB B p)
      (DividedPowers.Inseparable.completion p lam))
  | degree + 1 => inferInstanceAs (Module (completedRingB B p)
      (AdicCompletion (principalIdealB B p)
        (exteriorPower.form (DividedPowers.Inseparable.completion p lam)
          (inseparableOneForm A B δ p lam) (degree + 1))))

/-- Exterior powers of quotient one-forms have the native extension-ring action. -/
noncomputable instance inseparableAlgebraicFormExtensionModule (degree : ℕ) :
    Module (DividedPowers.Inseparable.completion p lam)
      (exteriorPower.form (DividedPowers.Inseparable.completion p lam)
        (inseparableOneForm A B δ p lam) degree) :=
  exteriorPower.form.module degree

/-- Base scalars act on the target exterior powers through the coefficient extension. -/
noncomputable instance inseparableAlgebraicFormBaseModule (degree : ℕ) :
    Module B (exteriorPower.form (DividedPowers.Inseparable.completion p lam)
      (inseparableOneForm A B δ p lam) degree) :=
  exteriorPower.form.moduleOfScalarTower degree

/-- Base scalars and extension scalars are compatible on the target exterior powers. -/
instance inseparableAlgebraicFormBaseTower (degree : ℕ) :
    IsScalarTower B (DividedPowers.Inseparable.completion p lam)
      (exteriorPower.form (DividedPowers.Inseparable.completion p lam)
        (inseparableOneForm A B δ p lam) degree) :=
  exteriorPower.form.isScalarTower_moduleOfScalarTower degree

/-- The two extension-ring actions on its exterior forms commute. -/
instance inseparableAlgebraicFormSMulComm (degree : ℕ) :
    SMulCommClass (DividedPowers.Inseparable.completion p lam)
      (DividedPowers.Inseparable.completion p lam)
      (exteriorPower.form (DividedPowers.Inseparable.completion p lam)
        (inseparableOneForm A B δ p lam) degree) :=
  ⟨fun r s form ↦ by rw [smul_smul, smul_smul, mul_comm]⟩

/-- Coefficient extension on completed divided-power forms. -/
noncomputable def inseparableFormMap : (degree : ℕ) →
    exteriorPower.completedForm B p (formB A B δ) degree →ₗ[completedRingB B p]
      inseparableForm A B δ p lam degree
  | 0 => (Algebra.linearMap (completedRingB B p)
      (DividedPowers.Inseparable.completion p lam))
  | degree + 1 => AdicCompletion.map (principalIdealB B p)
      (Connection.inducedForm (inseparableOneFormMap A B δ p lam) (degree + 1))

/-- Evaluation of formal additive basic forms in the target exterior powers. -/
private noncomputable def inseparableBasicEvaluation (degree : ℕ) :
    ((DividedPowers.Inseparable.completion p lam ×
      (Fin degree → DividedPowers.Inseparable.completion p lam)) →₀ ℤ) →+
      exteriorPower.form (DividedPowers.Inseparable.completion p lam)
        (inseparableOneForm A B δ p lam) degree :=
  (Finsupp.linearCombination ℤ (fun entries : DividedPowers.Inseparable.completion p lam ×
      (Fin degree → DividedPowers.Inseparable.completion p lam) ↦
    DifferentialOperator.DeRham.basicForm (inseparableDerivation A B δ p lam)
      degree entries.1 entries.2)).toAddMonoidHom

/-- Differentiation of a basic form differentiates its coefficient and prepends that differential. -/
private noncomputable def inseparableBasicDifferential (degree : ℕ) :
    ((DividedPowers.Inseparable.completion p lam ×
      (Fin degree → DividedPowers.Inseparable.completion p lam)) →₀ ℤ) →+
      exteriorPower.form (DividedPowers.Inseparable.completion p lam)
        (inseparableOneForm A B δ p lam) (degree + 1) :=
  (Finsupp.linearCombination ℤ (fun entries : DividedPowers.Inseparable.completion p lam ×
      (Fin degree → DividedPowers.Inseparable.completion p lam) ↦
    DifferentialOperator.DeRham.exactForm (inseparableDerivation A B δ p lam)
      (degree + 1) (Fin.cons entries.1 entries.2))).toAddMonoidHom

/-- A total representative of a form in the additive presentation by basic forms. -/
private noncomputable def inseparableBasicRepresentative (degree : ℕ) :=
  Function.invFun (inseparableBasicEvaluation A B δ p lam degree)

/-- The basic-form formula descends additively to each target exterior power. -/
theorem inseparableFormDifferential_laws (degree : ℕ) :
    let evaluation := (Finsupp.linearCombination ℤ (fun entries :
      DividedPowers.Inseparable.completion p lam ×
        (Fin degree → DividedPowers.Inseparable.completion p lam) ↦
      DifferentialOperator.DeRham.basicForm (inseparableDerivation A B δ p lam)
        degree entries.1 entries.2)).toAddMonoidHom
    let derivative := (Finsupp.linearCombination ℤ (fun entries :
      DividedPowers.Inseparable.completion p lam ×
        (Fin degree → DividedPowers.Inseparable.completion p lam) ↦
      DifferentialOperator.DeRham.exactForm (inseparableDerivation A B δ p lam)
        (degree + 1) (Fin.cons entries.1 entries.2))).toAddMonoidHom
    Function.Surjective evaluation ∧
      (∀ first second, evaluation first = evaluation second →
        derivative first = derivative second) := sorry

/-- The de Rham differential on the uncompleted quotient exterior powers. -/
private noncomputable def inseparableAlgebraicDifferential (degree : ℕ) :
    exteriorPower.form (DividedPowers.Inseparable.completion p lam)
      (inseparableOneForm A B δ p lam) degree →+
    exteriorPower.form (DividedPowers.Inseparable.completion p lam)
      (inseparableOneForm A B δ p lam) (degree + 1) :=
  AddMonoidHom.mk' (fun form ↦ inseparableBasicDifferential A B δ p lam degree
    (inseparableBasicRepresentative A B δ p lam degree form)) (by
      intro first second
      have surj := (inseparableFormDifferential_laws A B δ p lam degree).1
      change Function.Surjective (inseparableBasicEvaluation A B δ p lam degree) at surj
      have descent := (inseparableFormDifferential_laws A B δ p lam degree).2
      rw [← map_add]
      apply descent
      rw [map_add]
      change inseparableBasicEvaluation A B δ p lam degree
        (Function.invFun (inseparableBasicEvaluation A B δ p lam degree) (first + second)) =
          inseparableBasicEvaluation A B δ p lam degree
            (Function.invFun (inseparableBasicEvaluation A B δ p lam degree) first) +
          inseparableBasicEvaluation A B δ p lam degree
            (Function.invFun (inseparableBasicEvaluation A B δ p lam degree) second)
      rw [Function.rightInverse_invFun surj, Function.rightInverse_invFun surj,
        Function.rightInverse_invFun surj])

/-- The target differential is the continuous extension of the basic-form differential. -/
noncomputable def inseparableFormDifferential : (degree : ℕ) →
    inseparableForm A B δ p lam degree →+ inseparableForm A B δ p lam (degree + 1)
  | 0 => (AdicCompletion.of (principalIdealB B p) _).toAddMonoidHom.comp
      (inseparableAlgebraicDifferential A B δ p lam 0)
  | degree + 1 => AdicCompletion.completeAddMap B B p
      (inseparableAlgebraicDifferential A B δ p lam (degree + 1))

/-- Exterior multiplication by a base one-form, computed before or after completion
according to the degree of the second form. -/
private noncomputable def inseparableWedgeValue : (degree : ℕ) →
    exteriorPower.completedForm B p (formB A B δ) 1 →
      inseparableForm A B δ p lam degree → inseparableForm A B δ p lam (degree + 1)
  | 0 => fun first (coefficient : DividedPowers.Inseparable.completion p lam) ↦
      AdicCompletion.map (principalIdealB B p)
        (coefficient • inseparableOneFormMap A B δ p lam) first
  | degree + 1 => fun first second ↦
      AdicCompletion.completeBilinear B p
        (((wedge (DividedPowers.Inseparable.completion p lam)
          (Ω := inseparableOneForm A B δ p lam) 1 (degree + 1)).restrictScalars₁₂ B B).comp
          (inseparableOneFormMap A B δ p lam)) first second

/-- The canonical form comparison intertwines differentials, and completed exterior
multiplication is bilinear over the completed base ring. -/
theorem inseparableFormMap_laws :
    (∀ degree form,
      inseparableFormDifferential A B δ p lam degree
          (inseparableFormMap A B δ p lam degree form) =
        inseparableFormMap A B δ p lam (degree + 1)
          (completedBaseDifferential A B δ p degree form)) ∧
    (∀ degree,
      let value : exteriorPower.completedForm B p (formB A B δ) 1 →
        inseparableForm A B δ p lam degree → inseparableForm A B δ p lam (degree + 1) :=
        match degree with
        | 0 => fun first (coefficient : DividedPowers.Inseparable.completion p lam) ↦
            AdicCompletion.map (principalIdealB B p)
              (coefficient • (relationsB A B δ).liftQ
                (Derivation.liftKaehlerDifferential
                  ((inseparableDerivation A B δ p lam).compAlgebraMap B) :
                    Ω[B⁄A] →ₗ[B] inseparableOneForm A B δ p lam)
                (inseparableRelations_compatible A B δ p lam)) first
        | n + 1 => fun first second ↦
            AdicCompletion.completeBilinear B p
              (((wedge (DividedPowers.Inseparable.completion p lam)
          (Ω := inseparableOneForm A B δ p lam) 1 (n + 1)).restrictScalars₁₂ B B).comp
                ((relationsB A B δ).liftQ
                  (Derivation.liftKaehlerDifferential
                  ((inseparableDerivation A B δ p lam).compAlgebraMap B) :
                    Ω[B⁄A] →ₗ[B] inseparableOneForm A B δ p lam)
                  (inseparableRelations_compatible A B δ p lam))) first second
      (∀ first second third, value first (second + third) =
        value first second + value first third) ∧
      (∀ first (coefficient : completedRingB B p) second,
        value first (coefficient • second) = coefficient • value first second) ∧
      (∀ first second third, value (first + second) third =
        value first third + value second third) ∧
      (∀ (coefficient : completedRingB B p) first second,
        value (coefficient • first) second = coefficient • value first second)) := sorry

/-- Completed exterior multiplication by a completed base one-form. -/
noncomputable def inseparableLeftWedge (degree : ℕ) :
    exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      inseparableForm A B δ p lam degree →ₗ[completedRingB B p]
        inseparableForm A B δ p lam (degree + 1) where
  toFun first :=
    { toFun := inseparableWedgeValue A B δ p lam degree first
      map_add' := (inseparableFormMap_laws A B δ p lam).2 degree |>.1 first
      map_smul' := (inseparableFormMap_laws A B δ p lam).2 degree |>.2.1 first }
  map_add' first second := LinearMap.ext
    ((inseparableFormMap_laws A B δ p lam).2 degree |>.2.2.1 first second)
  map_smul' coefficient first := LinearMap.ext
    ((inseparableFormMap_laws A B δ p lam).2 degree |>.2.2.2 coefficient first)

/-- The divided-power ideal on the inseparable extension is generated by the base ideal
and all positive formal divided powers of the new coordinate. -/
noncomputable def inseparableIdeal : Ideal (DividedPowers.Inseparable.completion p lam) :=
  Ideal.span ((algebraMap B (DividedPowers.Inseparable.completion p lam)) '' (J : Set B) ∪
    Set.range (fun n : ℕ ↦ DividedPowers.Inseparable.xiPow p lam (n + 1)))

/-- The concrete quotient forms identify with completed divided-power differentials of the
extension, preserving coefficient derivations, exterior generators, and de Rham differentials. -/
theorem inseparableForms_spec [Fact p.Prime] [Algebra (Int.LocalizationAtPrime p) B]
    (h_nilpotent : IsNilpotent (p : B ⧸ J)) :
    ∃ γ : DividedPowers (inseparableIdeal B p lam (J := J)),
      (∀ n x, x ∈ J → γ.dpow n (algebraMap B _ x) = algebraMap B _ (δ.dpow n x)) ∧
      (∀ n, γ.dpow n (DividedPowers.Inseparable.xiPow p lam 1) =
        DividedPowers.Inseparable.xiPow p lam n) ∧
      ∃ equivalence : (degree : ℕ) → inseparableForm A B δ p lam degree ≃+
        exteriorPower.completedForm (DividedPowers.Inseparable.completion p lam) p
          (formB A (DividedPowers.Inseparable.completion p lam) γ) degree,
        (∀ coefficient : DividedPowers.Inseparable.completion p lam, equivalence 0 coefficient =
          AdicCompletion.of (principalIdealB (DividedPowers.Inseparable.completion p lam) p)
            (DividedPowers.Inseparable.completion p lam) coefficient) ∧
        (∀ degree coefficient entries,
          equivalence (degree + 1)
            (AdicCompletion.of (principalIdealB B p) _
              (DifferentialOperator.DeRham.basicForm (inseparableDerivation A B δ p lam)
                (degree + 1) coefficient entries)) =
            AdicCompletion.of (principalIdealB (DividedPowers.Inseparable.completion p lam) p) _
              (DifferentialOperator.DeRham.basicForm
                (derivationB A (DividedPowers.Inseparable.completion p lam) γ)
                (degree + 1) coefficient entries)) ∧
        (∀ degree form, equivalence (degree + 1)
          (inseparableFormDifferential A B δ p lam degree form) =
          AdicCompletion.completeAddMap (DividedPowers.Inseparable.completion p lam)
            (DividedPowers.Inseparable.completion p lam) p
            (canonicalFamily A (DividedPowers.Inseparable.completion p lam) γ degree).toAddMonoidHom
            (equivalence degree form)) := sorry

variable {M : Type u} [AddCommGroup M] [Module (completedRingB B p) M]

/-- The tensor Leibniz formula combines the given connection with exterior differentiation. -/
private noncomputable def inseparablePairingValue (conn : Adic A B δ p M) (degree : ℕ)
    (element : M) (form : inseparableForm A B δ p lam degree) :
    completedTensorB (completedRingB B p) p M
      (inseparableForm A B δ p lam (degree + 1)) :=
  AdicCompletion.map (principalIdealB (completedRingB B p) p)
    (TensorProduct.map (LinearMap.id : M →ₗ[completedRingB B p] M)
      ((inseparableLeftWedge A B δ p lam degree).flip form))
    (conn.toAddMonoidHom element) +
  AdicCompletion.of (principalIdealB (completedRingB B p) p) _
    (element ⊗ₜ[completedRingB B p] inseparableFormDifferential A B δ p lam degree form)

/-- The tensor Leibniz formula is additive in both entries and balanced over the completed
base ring. -/
theorem inseparablePairing_laws (conn : Adic A B δ p M) (degree : ℕ) :
    let value := fun (element : M) (form : inseparableForm A B δ p lam degree) ↦
      AdicCompletion.map (principalIdealB (completedRingB B p) p)
        (TensorProduct.map (LinearMap.id : M →ₗ[completedRingB B p] M)
          ((inseparableLeftWedge A B δ p lam degree).flip form))
        (conn.toAddMonoidHom element) +
      AdicCompletion.of (principalIdealB (completedRingB B p) p) _
        (element ⊗ₜ[completedRingB B p] inseparableFormDifferential A B δ p lam degree form)
    (∀ element first second, value element (first + second) =
      value element first + value element second) ∧
    (∀ first second form, value (first + second) form =
      value first form + value second form) ∧
    (∀ (coefficient : completedRingB B p) element form,
      value (coefficient • element) form = value element (coefficient • form)) := sorry

/-- The additive, balanced connection pairing on target forms. -/
noncomputable def inseparablePairing (conn : Adic A B δ p M) (degree : ℕ) :
    M →+ inseparableForm A B δ p lam degree →+
      completedTensorB (completedRingB B p) p M
        (inseparableForm A B δ p lam (degree + 1)) :=
  AddMonoidHom.mk' (fun element ↦
    AddMonoidHom.mk' (inseparablePairingValue A B δ p lam conn degree element)
      ((inseparablePairing_laws A B δ p lam conn degree).1 element))
    (fun first second ↦ AddMonoidHom.ext
      ((inseparablePairing_laws A B δ p lam conn degree).2.1 first second))

/-- The differential after completed coefficient extension is the continuous extension of
the balanced tensor Leibniz pairing. -/
noncomputable def inseparableDifferential (conn : Adic A B δ p M) (degree : ℕ) :
    completedTensorB (completedRingB B p) p M (inseparableForm A B δ p lam degree) →+
      completedTensorB (completedRingB B p) p M
        (inseparableForm A B δ p lam (degree + 1)) :=
  AdicCompletion.extendCompleteAddMap (completedRingB B p) p
    (TensorProduct.liftAddHom (inseparablePairing A B δ p lam conn degree)
      (inseparablePairing_laws A B δ p lam conn degree).2.2)

variable (M) in
/-- Each target degree is the completed tensor product of coefficients with target forms,
including completed coefficient extension in degree zero. -/
@[expose]
noncomputable def inseparableTerm (degree : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of
    (completedTensorB (completedRingB B p) p M (inseparableForm A B δ p lam degree))

/-- An integrable completed-valued connection gives a square-zero target differential. -/
theorem inseparableDifferential_sq (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) (degree : ℕ) :
    AddCommGrpCat.ofHom (inseparableDifferential A B δ p lam conn degree) ≫
      AddCommGrpCat.ofHom (inseparableDifferential A B δ p lam conn (degree + 1)) = 0 := sorry

/-- The de Rham complex after completed inseparable coefficient extension. -/
@[expose]
noncomputable def inseparableComplex (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (inseparableTerm A B δ p lam M)
    (fun degree ↦ AddCommGrpCat.ofHom (inseparableDifferential A B δ p lam conn degree))
    (inseparableDifferential_sq A B δ p lam conn hconn)

variable (M) in
/-- The canonical comparison sends a coefficient to its tensor with one in degree zero
and extends the form factor in every positive degree. -/
noncomputable def inseparableComparisonComponent : (degree : ℕ) →
    term A B δ p M degree ⟶ inseparableTerm A B δ p lam M degree
  | 0 => AddCommGrpCat.ofHom
      ((AdicCompletion.of (principalIdealB (completedRingB B p) p) _).comp
        ((TensorProduct.mk (completedRingB B p) M
          (DividedPowers.Inseparable.completion p lam)).flip 1)).toAddMonoidHom
  | degree + 1 => AddCommGrpCat.ofHom
      (AdicCompletion.map (principalIdealB (completedRingB B p) p)
        (TensorProduct.map (LinearMap.id : M →ₗ[completedRingB B p] M)
          (inseparableFormMap A B δ p lam (degree + 1)))).toAddMonoidHom

/-- Canonical coefficient-and-form extension commutes with the connection differentials. -/
theorem inseparableComparison_comm (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) (degree : ℕ) :
    inseparableComparisonComponent A B δ p lam M degree ≫
      (inseparableComplex A B δ p lam conn hconn).d degree (degree + 1) =
    (deRhamComplex A B δ p conn hconn).d degree (degree + 1) ≫
      inseparableComparisonComponent A B δ p lam M (degree + 1) := sorry

/-- The canonical comparison of completed connection complexes along the inseparable extension. -/
@[expose]
noncomputable def inseparableComparison (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) :
    deRhamComplex A B δ p conn hconn ⟶ inseparableComplex A B δ p lam conn hconn :=
  CochainComplex.ofHom (inseparableComparisonComponent A B δ p lam M)
    (inseparableComparison_comm A B δ p lam conn hconn)

/-- The canonical comparison has exactly the coefficient-and-form components specified above. -/
theorem inseparableComparison_apply (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) (degree : ℕ) (element : term A B δ p M degree) :
    (inseparableComparison A B δ p lam conn hconn).f degree element =
      inseparableComparisonComponent A B δ p lam M degree element := rfl

/-- The completed inseparable comparison admits a single reverse map whose two composites
are homotopic to multiplication by the prime. -/
theorem existsInseparableReverseComparisonHomotopy [Fact p.Prime]
    [Algebra (Int.LocalizationAtPrime p) B]
    (h_nilpotent : IsNilpotent (p : B ⧸ J))
    [IsAdicComplete (principalIdealB (completedRingB B p) p) M]
    (conn : Adic A B δ p M) (hconn : IsIntegrable A B δ p conn) :
    ∃ e : inseparableComplex A B δ p lam conn hconn ⟶ deRhamComplex A B δ p conn hconn,
      Nonempty (Homotopy (inseparableComparison A B δ p lam conn hconn ≫ e)
        (p • 𝟙 (deRhamComplex A B δ p conn hconn))) ∧
      Nonempty (Homotopy (e ≫ inseparableComparison A B δ p lam conn hconn)
        (p • 𝟙 (inseparableComplex A B δ p lam conn hconn))) := sorry

end Connection.Adic
