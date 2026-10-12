/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.PrincipalMaps
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.PolynomialPoincare
public import ReasLib.RingTheory.Kaehler.DeRham.Connection
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.BaseChange

@[expose] public section

open CategoryTheory
open DPPolynomial.DeRham
open scoped TensorProduct

universe u

namespace DPPolynomial.DeRham

/-- The principal ideal `(p)` of `B` used for p-adic completion. -/
noncomputable abbrev principalIdealB (B : Type u) [CommRing B] (p : ℕ) : Ideal B :=
  AdicCompletion.principalIdeal B p

/-- The principal ideal `(p)` of `P` used for p-adic completion. -/
noncomputable abbrev principalIdealP (B : Type u) [CommRing B] (ι : Type u) (p : ℕ) :
    Ideal (DPPolynomial B ι) :=
  AdicCompletion.principalIdeal (DPPolynomial B ι) p

/-- The p-adic completion `D` of `B`. -/
noncomputable abbrev completedRingB (B : Type u) [CommRing B] (p : ℕ) : Type u :=
  AdicCompletion (principalIdealB B p) B

/-- The p-adic completion `D'` of `P`. -/
noncomputable abbrev completedRingP (B : Type u) [CommRing B] (ι : Type u) (p : ℕ) : Type u :=
  AdicCompletion (principalIdealP B ι p) (DPPolynomial B ι)

/-- Degree-`i` completed forms as the p-adic completion of exterior forms. -/
noncomputable abbrev completedForm (B : Type u) [CommRing B] (p : ℕ)
    (Ω : Type u) [AddCommGroup Ω] [Module B Ω] (i : ℕ) : Type u :=
  AdicCompletion (principalIdealB B p) (exteriorPower.form B Ω i)

/-- Completed forms are p-adic completions of uncompleted exterior forms. -/
theorem completedForm_spec (B : Type u) [CommRing B] (p : ℕ)
    (Ω : Type u) [AddCommGroup Ω] [Module B Ω] (i : ℕ) :
    completedForm B p Ω i =
      AdicCompletion (principalIdealB B p) (exteriorPower.form B Ω i) := sorry

/-- Completed tensor `M ⊗^∧[B] N` as the p-adic completion of `M ⊗[B] N`. -/
noncomputable abbrev completedTensorB (B : Type u) [CommRing B] (p : ℕ) (M N : Type u)
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] : Type u :=
  AdicCompletion (principalIdealB B p) (M ⊗[B] N)

/-- Completed tensor is the p-adic completion of the ordinary tensor product over `B`. -/
theorem completedTensorB_spec (B : Type u) [CommRing B] (p : ℕ) (M N : Type u)
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] :
    completedTensorB B p M N = AdicCompletion (principalIdealB B p) (M ⊗[B] N) := sorry

section CompletedForms

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J) (ι : Type u) (p : ℕ)

/-- Completed polynomial forms, restricting scalars before completion; the principal p-adic
filtration is unchanged by this restriction. Degree zero is `D'`. -/
noncomputable abbrev completedPolynomialForm (degree : ℕ) : Type u :=
  AdicCompletion (principalIdealB B p)
    (exteriorPower.form (DPPolynomial B ι)
      (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree)

/-- Restricting coefficients to `B` does not change the p-adic completion of polynomial forms. -/
noncomputable def completedPolynomialFormEquiv (degree : ℕ) :
    completedPolynomialForm A B δ ι p degree ≃+
      completedForm (DPPolynomial B ι) p
        (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree where
  toFun := AdicCompletion.completeAddMap B (DPPolynomial B ι) p (AddMonoidHom.id _)
  invFun := AdicCompletion.completeAddMap (DPPolynomial B ι) B p (AddMonoidHom.id _)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The completion bridge is the identity on the original polynomial forms. -/
theorem completedPolynomialFormEquiv_of (degree : ℕ)
    (form : exteriorPower.form (DPPolynomial B ι)
      (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree) :
    completedPolynomialFormEquiv A B δ ι p degree
        (AdicCompletion.of (principalIdealB B p) _ form) =
      AdicCompletion.of (principalIdealP B ι p) _ form := sorry

/-- The completed coefficient-and-form map is induced from the canonical scalar extension. -/
noncomputable def completedFormComparison (degree : ℕ) :
    completedForm B p (formB A B δ) degree →ₗ[completedRingB B p]
      completedPolynomialForm A B δ ι p degree :=
  AdicCompletion.map (principalIdealB B p)
    (Connection.inducedForm (coefficientFormMap A B δ ι) degree)

/-- The derivative on `D` is the continuous extension of the divided-power derivation on `B`. -/
noncomputable def completedDerivation :
    completedRingB B p →+ completedForm B p (formB A B δ) 1 :=
  AdicCompletion.completeAddMap B B p (derivationB A B δ).toLinearMap.toAddMonoidHom

/-- The derivative of completed base forms is defined without an algebraic lift of a connection. -/
noncomputable def completedBaseDifferential (degree : ℕ) :
    completedForm B p (formB A B δ) degree →+
      completedForm B p (formB A B δ) (degree + 1) :=
  AdicCompletion.completeAddMap B B p (canonicalFamily A B δ degree).toAddMonoidHom

/-- Wedge by a completed one-form in the completed base forms. -/
noncomputable def completedBaseLeftWedge (degree : ℕ) :
    completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedForm B p (formB A B δ) degree →ₗ[completedRingB B p]
        completedForm B p (formB A B δ) (degree + 1) :=
  AdicCompletion.completeBilinear B p ((canonicalCalculus A B δ).leftWedge degree)

end CompletedForms

end DPPolynomial.DeRham

namespace Connection

universe v

section AlgebraicCompletion

variable {A B Ω M : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable [AddCommGroup M] [Module B M]
variable {D : Derivation A B Ω} {family : DifferentialOperator.DeRham.Family A B Ω}

/-- Degreewise principal-adic completion of the terms of an algebraic connection. -/
noncomputable def completedDeRhamTerm (conn : Connection D M) (p : ℕ) : ℕ → AddCommGrpCat
  | 0 => AddCommGrpCat.of (AdicCompletion (AdicCompletion.principalIdeal B p) M)
  | degree + 1 => AddCommGrpCat.of
      (AdicCompletion (AdicCompletion.principalIdeal B p)
        (M ⊗[B] exteriorPower.form B Ω (degree + 1)))

/-- The completed algebraic de Rham differentials are the additive principal-adic extensions. -/
noncomputable def completedDeRhamDifferential (conn : Connection D M)
    (calculus : ExteriorCalculus D family) (p : ℕ) :
    (degree : ℕ) → completedDeRhamTerm conn p degree ⟶
      completedDeRhamTerm conn p (degree + 1)
  | 0 => AddCommGrpCat.ofHom (AdicCompletion.completeAddMap B B p conn.toAddMonoidHom)
  | degree + 1 => AddCommGrpCat.ofHom
      (AdicCompletion.completeAddMap B B p (differential conn calculus (degree + 1)))

/-- Degreewise principal-adic completion of the de Rham complex of an integrable algebraic connection. -/
noncomputable def completedDeRhamComplex {conn : Connection D M}
    (calculus : ExteriorCalculus D family) (hconn : IsIntegrable conn calculus) (p : ℕ) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (completedDeRhamTerm conn p)
    (completedDeRhamDifferential conn calculus p) (fun _ ↦ sorry)

end AlgebraicCompletion

/-- A connection valued in completed tensors over the p-adic coefficient ring `D`.
No algebraic lift of its values is required. -/
structure Adic (A B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
    (M : Type v) [AddCommGroup M] [Module (completedRingB B p) M] where
  toAddMonoidHom : M →+
    completedTensorB (completedRingB B p) p M (completedForm B p (formB A B δ) 1)
  leibniz (coefficient : completedRingB B p) (element : M) :
    toAddMonoidHom (coefficient • element) = coefficient • toAddMonoidHom element +
      AdicCompletion.of (principalIdealB (completedRingB B p) p) _
        (element ⊗ₜ[completedRingB B p] completedDerivation A B δ p coefficient)

namespace Adic

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
variable {M : Type u} [AddCommGroup M] [Module (completedRingB B p) M]

/-- Construct a completed-valued connection from its additive map and Leibniz law. -/
def of (map : M →+
    completedTensorB (completedRingB B p) p M (completedForm B p (formB A B δ) 1))
    (leibniz : ∀ (coefficient : completedRingB B p) (element : M),
      map (coefficient • element) = coefficient • map element +
        AdicCompletion.of (principalIdealB (completedRingB B p) p) _
          (element ⊗ₜ[completedRingB B p] completedDerivation A B δ p coefficient)) :
    Adic A B δ p M :=
  { toAddMonoidHom := map, leibniz := leibniz }

/-- The completed connection constructor preserves its specified map. -/
theorem of_toAddMonoidHom (conn : Adic A B δ p M) :
    (of A B δ p conn.toAddMonoidHom conn.leibniz).toAddMonoidHom =
      conn.toAddMonoidHom := sorry

/-- A completed-valued connection retains its defining Leibniz law. -/
theorem apply_leibniz (conn : Adic A B δ p M) (coefficient : completedRingB B p)
    (element : M) :
    conn.toAddMonoidHom (coefficient • element) = coefficient • conn.toAddMonoidHom element +
      AdicCompletion.of (principalIdealB (completedRingB B p) p) _
        (element ⊗ₜ[completedRingB B p] completedDerivation A B δ p coefficient) := sorry

/-- The connection Leibniz pairing with completed base forms. -/
noncomputable def pairing (conn : Adic A B δ p M) (degree : ℕ) :
    M →+ completedForm B p (formB A B δ) degree →+
      completedTensorB (completedRingB B p) p M (completedForm B p (formB A B δ) (degree + 1)) where
  toFun element :=
    { toFun := fun form ↦
        (AdicCompletion.map (principalIdealB (completedRingB B p) p)
          (TensorProduct.map (LinearMap.id : M →ₗ[completedRingB B p] M)
            ((completedBaseLeftWedge A B δ p degree).flip form))
          (conn.toAddMonoidHom element) :
            completedTensorB (completedRingB B p) p M
              (completedForm B p (formB A B δ) (degree + 1))) +
        (AdicCompletion.of (principalIdealB (completedRingB B p) p)
          (M ⊗[completedRingB B p] completedForm B p (formB A B δ) (degree + 1)))
          (element ⊗ₜ[completedRingB B p] completedBaseDifferential A B δ p degree form)
      map_zero' := sorry
      map_add' := sorry }
  map_zero' := sorry
  map_add' := sorry

/-- The extended connection differential on completed tensor products. -/
noncomputable def differential (conn : Adic A B δ p M) (degree : ℕ) :
    completedTensorB (completedRingB B p) p M (completedForm B p (formB A B δ) degree) →+
      completedTensorB (completedRingB B p) p M (completedForm B p (formB A B δ) (degree + 1)) :=
  AdicCompletion.extendCompleteAddMap (completedRingB B p) p
    (TensorProduct.liftAddHom (pairing A B δ p conn degree) sorry)

/-- The completed source differential is the continuous extension of its Leibniz pairing. -/
theorem differential_tmul (conn : Adic A B δ p M) (degree : ℕ) (element : M)
    (form : completedForm B p (formB A B δ) degree) :
    differential A B δ p conn degree
        (AdicCompletion.of (principalIdealB (completedRingB B p) p) _
          (element ⊗ₜ[completedRingB B p] form)) =
      pairing A B δ p conn degree element form := sorry

/-- Integrability is vanishing of the curvature of the completed-valued connection. -/
def IsIntegrable (conn : Adic A B δ p M) : Prop :=
  (differential A B δ p conn 1).comp conn.toAddMonoidHom = 0

/-- Integrability is precisely the completed curvature-zero identity. -/
theorem isIntegrable_iff (conn : Adic A B δ p M) :
    IsIntegrable A B δ p conn ↔
      (differential A B δ p conn 1).comp conn.toAddMonoidHom = 0 := sorry

variable (M) in
/-- The completed source complex has the original complete module in degree zero. -/
noncomputable def term : ℕ → AddCommGrpCat
  | 0 => AddCommGrpCat.of M
  | degree + 1 => AddCommGrpCat.of
      (completedTensorB (completedRingB B p) p M (completedForm B p (formB A B δ) (degree + 1)))

/-- The source differential starts with the given completed-valued connection. -/
noncomputable def deRhamDifferential (conn : Adic A B δ p M) :
    (degree : ℕ) → term A B δ p M degree ⟶ term A B δ p M (degree + 1)
  | 0 => AddCommGrpCat.ofHom conn.toAddMonoidHom
  | degree + 1 => AddCommGrpCat.ofHom (differential A B δ p conn (degree + 1))

/-- Degree zero of the completed source terms is the given module itself. -/
theorem term_zero : term A B δ p M 0 = AddCommGrpCat.of M := sorry

/-- The completed source differential starts with the specified connection. -/
theorem deRhamDifferential_zero (conn : Adic A B δ p M) :
    deRhamDifferential A B δ p conn 0 = AddCommGrpCat.ofHom conn.toAddMonoidHom := sorry

/-- The de Rham complex of an integrable completed-valued connection. -/
noncomputable def deRhamComplex (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (term A B δ p M) (deRhamDifferential A B δ p conn) (fun _ ↦ sorry)

/-- The source de Rham complex starts with its specified complete module and connection. -/
theorem deRhamComplex_zero (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) :
    (deRhamComplex A B δ p conn hconn).X 0 = AddCommGrpCat.of M := sorry

end Adic

end Connection

end
