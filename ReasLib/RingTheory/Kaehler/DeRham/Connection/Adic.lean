/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorPower.AdicCompletion
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

private theorem completeAddMap_id_leftInverse
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ)
    (U : Type u) [AddCommGroup U] [Module R U] [Module S U] :
    Function.LeftInverse (AdicCompletion.completeAddMap S R p (AddMonoidHom.id U))
      (AdicCompletion.completeAddMap R S p (AddMonoidHom.id U)) := by
  intro element
  apply AdicCompletion.ext
  intro degree
  simp only [AdicCompletion.completeAddMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact Quotient.inductionOn (element.val degree) (fun _ ↦ rfl)

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

/-- Completed tensor `M ⊗^∧[B] N` as the p-adic completion of `M ⊗[B] N`. -/
noncomputable abbrev completedTensorB (B : Type u) [CommRing B] (p : ℕ) (M N : Type u)
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] : Type u :=
  AdicCompletion (principalIdealB B p) (M ⊗[B] N)

/-- Completed tensor is the p-adic completion of the ordinary tensor product over `B`. -/
theorem completedTensorB_spec (B : Type u) [CommRing B] (p : ℕ) (M N : Type u)
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] :
    completedTensorB B p M N = AdicCompletion (principalIdealB B p) (M ⊗[B] N) := rfl

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
      exteriorPower.completedForm (DPPolynomial B ι) p
        (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree where
  toFun := AdicCompletion.completeAddMap B (DPPolynomial B ι) p (AddMonoidHom.id _)
  invFun := AdicCompletion.completeAddMap (DPPolynomial B ι) B p (AddMonoidHom.id _)
  left_inv := by exact completeAddMap_id_leftInverse B (DPPolynomial B ι) p _
  right_inv := by exact completeAddMap_id_leftInverse (DPPolynomial B ι) B p _
  map_add' := (AdicCompletion.completeAddMap B (DPPolynomial B ι) p
    (AddMonoidHom.id _)).map_add

/-- The completion bridge is the identity on the original polynomial forms. -/
theorem completedPolynomialFormEquiv_of (degree : ℕ)
    (form : exteriorPower.form (DPPolynomial B ι)
      (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree) :
    completedPolynomialFormEquiv A B δ ι p degree
        (AdicCompletion.of (principalIdealB B p) _ form) =
      AdicCompletion.of (principalIdealP B ι p) _ form := rfl

/-- The completed coefficient-and-form map is induced from the canonical scalar extension. -/
noncomputable def completedFormComparison (degree : ℕ) :
    exteriorPower.completedForm B p (formB A B δ) degree →ₗ[completedRingB B p]
      completedPolynomialForm A B δ ι p degree :=
  AdicCompletion.map (principalIdealB B p)
    (Connection.inducedForm (coefficientFormMap A B δ ι) degree)

/-- The derivative on `D` is the continuous extension of the divided-power derivation on `B`. -/
noncomputable def completedDerivation :
    completedRingB B p →+ exteriorPower.completedForm B p (formB A B δ) 1 :=
  AdicCompletion.completeAddMap B B p (derivationB A B δ).toLinearMap.toAddMonoidHom

/-- The derivative of completed base forms is defined without an algebraic lift of a connection. -/
noncomputable def completedBaseDifferential (degree : ℕ) :
    exteriorPower.completedForm B p (formB A B δ) degree →+
      exteriorPower.completedForm B p (formB A B δ) (degree + 1) :=
  AdicCompletion.completeAddMap B B p (canonicalFamily A B δ degree).toAddMonoidHom

/-- Wedge by a completed one-form in the completed base forms. -/
noncomputable def completedBaseLeftWedge (degree : ℕ) :
    exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      exteriorPower.completedForm B p (formB A B δ) degree →ₗ[completedRingB B p]
        exteriorPower.completedForm B p (formB A B δ) (degree + 1) :=
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

private theorem completeAddMap_comp_zero
    {U V W : Type u} [AddCommGroup U] [Module B U]
    [AddCommGroup V] [Module B V] [AddCommGroup W] [Module B W]
    (p : ℕ) (first : U →+ V) (second : V →+ W) (h : second.comp first = 0) :
    (AdicCompletion.completeAddMap B B p second).comp
      (AdicCompletion.completeAddMap B B p first) = 0 := by
  apply AddMonoidHom.ext
  intro element
  apply AdicCompletion.ext
  intro degree
  change (AdicCompletion.completeAddMap B B p second
    (AdicCompletion.completeAddMap B B p first element)).val degree = 0
  simp only [AdicCompletion.completeAddMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  refine Quotient.inductionOn (element.val degree) ?_
  intro representative
  have h_zero : second (first representative) = 0 := DFunLike.congr_fun h representative
  change (Submodule.Quotient.mk (second (first representative)) :
    W ⧸ ((AdicCompletion.principalIdeal B p) ^ degree • (⊤ : Submodule B W))) = 0
  rw [h_zero]
  rfl

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
    (completedDeRhamDifferential conn calculus p) (fun degree ↦ by
      apply AddCommGrpCat.hom_ext
      cases degree with
      | zero => exact completeAddMap_comp_zero p _ _ hconn
      | succ degree =>
        exact completeAddMap_comp_zero p _ _
          (squaresToZero_of_isIntegrable conn calculus hconn degree))

end AlgebraicCompletion

/-- A connection valued in completed tensors over the p-adic coefficient ring `D`.
No algebraic lift of its values is required. -/
structure Adic (A B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
    (M : Type v) [AddCommGroup M] [Module (completedRingB B p) M] where
  toAddMonoidHom : M →+
    completedTensorB (completedRingB B p) p M (exteriorPower.completedForm B p (formB A B δ) 1)
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
    completedTensorB (completedRingB B p) p M (exteriorPower.completedForm B p (formB A B δ) 1))
    (leibniz : ∀ (coefficient : completedRingB B p) (element : M),
      map (coefficient • element) = coefficient • map element +
        AdicCompletion.of (principalIdealB (completedRingB B p) p) _
          (element ⊗ₜ[completedRingB B p] completedDerivation A B δ p coefficient)) :
    Adic A B δ p M :=
  { toAddMonoidHom := map, leibniz := leibniz }

/-- The completed connection constructor preserves its specified map. -/
theorem of_toAddMonoidHom (conn : Adic A B δ p M) :
    (of A B δ p conn.toAddMonoidHom conn.leibniz).toAddMonoidHom =
      conn.toAddMonoidHom := rfl

/-- A completed-valued connection retains its defining Leibniz law. -/
theorem apply_leibniz (conn : Adic A B δ p M) (coefficient : completedRingB B p)
    (element : M) :
    conn.toAddMonoidHom (coefficient • element) = coefficient • conn.toAddMonoidHom element +
      AdicCompletion.of (principalIdealB (completedRingB B p) p) _
        (element ⊗ₜ[completedRingB B p] completedDerivation A B δ p coefficient) :=
  conn.leibniz coefficient element

private theorem completedMap_add_apply
    {R U V : Type u} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (I : Ideal R) (first second : U →ₗ[R] V)
    (element : AdicCompletion I U) :
    AdicCompletion.map I (first + second) element =
      AdicCompletion.map I first element + AdicCompletion.map I second element := by
  apply AdicCompletion.ext
  intro degree
  simp only [AdicCompletion.map_val_apply, AdicCompletion.val_add_apply]
  refine Quotient.inductionOn (element.val degree) ?_
  intro representative
  rfl

/-- The connection Leibniz pairing with completed base forms. -/
noncomputable def pairing (conn : Adic A B δ p M) (degree : ℕ) :
    M →+ exteriorPower.completedForm B p (formB A B δ) degree →+
      completedTensorB (completedRingB B p) p M (exteriorPower.completedForm B p (formB A B δ) (degree + 1)) where
  toFun element :=
    { toFun := fun form ↦
        (AdicCompletion.map (principalIdealB (completedRingB B p) p)
          (TensorProduct.map (LinearMap.id : M →ₗ[completedRingB B p] M)
            ((completedBaseLeftWedge A B δ p degree).flip form))
          (conn.toAddMonoidHom element) :
            completedTensorB (completedRingB B p) p M
              (exteriorPower.completedForm B p (formB A B δ) (degree + 1))) +
        (AdicCompletion.of (principalIdealB (completedRingB B p) p)
          (M ⊗[completedRingB B p] exteriorPower.completedForm B p (formB A B δ) (degree + 1)))
          (element ⊗ₜ[completedRingB B p] completedBaseDifferential A B δ p degree form)
      map_zero' := by
        rw [map_zero (completedBaseLeftWedge A B δ p degree).flip,
          TensorProduct.map_zero_right, AdicCompletion.map_zero,
          map_zero (completedBaseDifferential A B δ p degree), TensorProduct.tmul_zero,
          map_zero, LinearMap.zero_apply, zero_add]
      map_add' := by
        intro first second
        rw [map_add (completedBaseLeftWedge A B δ p degree).flip,
          TensorProduct.map_add_right, completedMap_add_apply,
          map_add (completedBaseDifferential A B δ p degree), TensorProduct.tmul_add,
          map_add]
        exact add_add_add_comm _ _ _ _ }
  map_zero' := by
    apply AddMonoidHom.ext
    intro form
    dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
    rw [map_zero conn.toAddMonoidHom, map_zero, TensorProduct.zero_tmul, map_zero,
      zero_add]
  map_add' := by
    intro first second
    apply AddMonoidHom.ext
    intro form
    dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
    rw [map_add conn.toAddMonoidHom, map_add, TensorProduct.add_tmul, map_add]
    exact add_add_add_comm _ _ _ _

private theorem completionDifferential_smul
    (R : Type u) [CommRing R] (p : ℕ)
    {E F G : Type u} [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (deriv : R →+ E) (diff : F →+ G) (wedge : E →ₗ[R] F →ₗ[R] G)
    (h : ∀ (r : R) (x : F), diff (r • x) = wedge (deriv r) x + r • diff x)
    (r : AdicCompletion (AdicCompletion.principalIdeal R p) R)
    (x : AdicCompletion (AdicCompletion.principalIdeal R p) F) :
    AdicCompletion.completeAddMap R R p diff (r • x) =
      AdicCompletion.completeBilinear R p wedge
        (AdicCompletion.completeAddMap R R p deriv r) x +
        r • AdicCompletion.completeAddMap R R p diff x := by
  apply AdicCompletion.ext
  intro degree
  simp only [AdicCompletion.completeAddMap, AdicCompletion.completeBilinear,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    AdicCompletion.smul_eval, AdicCompletion.val_add_apply]
  refine Quotient.inductionOn₂ (r.val degree) (x.val degree) ?_
  intro coefficient form
  change (Submodule.Quotient.mk (diff (coefficient • form)) :
    G ⧸ ((AdicCompletion.principalIdeal R p) ^ degree • (⊤ : Submodule R G))) =
      Submodule.Quotient.mk (wedge (deriv coefficient) form) +
        Submodule.Quotient.mk (coefficient • diff form)
  rw [h]
  rfl

private theorem completedMap_smul_apply
    {R U V : Type u} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (I : Ideal R) (r : R) (map : U →ₗ[R] V)
    (element : AdicCompletion I U) :
    AdicCompletion.map I (r • map) element = r • AdicCompletion.map I map element := by
  apply AdicCompletion.ext
  intro degree
  simp only [AdicCompletion.map_val_apply, AdicCompletion.val_smul_apply]
  refine Quotient.inductionOn (element.val degree) ?_
  intro representative
  rfl

private theorem completionPairing_balanced
    (R : Type u) [CommRing R] (I : Ideal R)
    {M E F G : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (deriv : R →+ E) (diff : F →+ G) (wedge : E →ₗ[R] F →ₗ[R] G)
    (conn : M →+ AdicCompletion I (M ⊗[R] E))
    (hleibniz : ∀ (r : R) (m : M), conn (r • m) = r • conn m +
      AdicCompletion.of I _ (m ⊗ₜ[R] deriv r))
    (hdiff : ∀ (r : R) (x : F), diff (r • x) = wedge (deriv r) x + r • diff x)
    (r : R) (m : M) (form : F) :
    AdicCompletion.map I (TensorProduct.map (LinearMap.id : M →ₗ[R] M) (wedge.flip form))
        (conn (r • m)) + AdicCompletion.of I _ ((r • m) ⊗ₜ[R] diff form) =
      AdicCompletion.map I (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (wedge.flip (r • form))) (conn m) +
        AdicCompletion.of I _ (m ⊗ₜ[R] diff (r • form)) := by
  rw [hleibniz, map_add, LinearMap.map_smul_of_tower, AdicCompletion.map_of,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.flip_apply, hdiff,
    map_smul wedge.flip, TensorProduct.map_smul_right, completedMap_smul_apply,
    TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul,
    map_add, map_smul]
  simp only [TensorProduct.tmul_smul, map_smul]
  abel

/-- The extended connection differential on completed tensor products. -/
noncomputable def differential (conn : Adic A B δ p M) (degree : ℕ) :
    completedTensorB (completedRingB B p) p M (exteriorPower.completedForm B p (formB A B δ) degree) →+
      completedTensorB (completedRingB B p) p M (exteriorPower.completedForm B p (formB A B δ) (degree + 1)) :=
  AdicCompletion.extendCompleteAddMap (completedRingB B p) p
    (TensorProduct.liftAddHom (pairing A B δ p conn degree) (by
      intro coefficient element form
      refine completionPairing_balanced (completedRingB B p) _
        (completedDerivation A B δ p) (completedBaseDifferential A B δ p degree)
        (completedBaseLeftWedge A B δ p degree) conn.toAddMonoidHom conn.leibniz ?_
        coefficient element form
      intro coefficient form
      exact completionDifferential_smul B p
        (derivationB A B δ).toLinearMap.toAddMonoidHom
        (canonicalFamily A B δ degree).toAddMonoidHom
        ((canonicalCalculus A B δ).leftWedge degree)
        ((canonicalCalculus A B δ).differential_smul degree) coefficient form))

/-- The completed source differential is the continuous extension of its Leibniz pairing. -/
theorem differential_tmul (conn : Adic A B δ p M) (degree : ℕ) (element : M)
    (form : exteriorPower.completedForm B p (formB A B δ) degree) :
    differential A B δ p conn degree
        (AdicCompletion.of (principalIdealB (completedRingB B p) p) _
          (element ⊗ₜ[completedRingB B p] form)) =
      pairing A B δ p conn degree element form := rfl

/-- Integrability is vanishing of the curvature of the completed-valued connection. -/
def IsIntegrable (conn : Adic A B δ p M) : Prop :=
  (differential A B δ p conn 1).comp conn.toAddMonoidHom = 0

/-- Integrability is precisely the completed curvature-zero identity. -/
theorem isIntegrable_iff (conn : Adic A B δ p M) :
    IsIntegrable A B δ p conn ↔
      (differential A B δ p conn 1).comp conn.toAddMonoidHom = 0 := Iff.rfl

variable (M) in
/-- The completed source complex has the original complete module in degree zero. -/
noncomputable def term : ℕ → AddCommGrpCat
  | 0 => AddCommGrpCat.of M
  | degree + 1 => AddCommGrpCat.of
      (completedTensorB (completedRingB B p) p M (exteriorPower.completedForm B p (formB A B δ) (degree + 1)))

/-- The source differential starts with the given completed-valued connection. -/
noncomputable def deRhamDifferential (conn : Adic A B δ p M) :
    (degree : ℕ) → term A B δ p M degree ⟶ term A B δ p M (degree + 1)
  | 0 => AddCommGrpCat.ofHom conn.toAddMonoidHom
  | degree + 1 => AddCommGrpCat.ofHom (differential A B δ p conn (degree + 1))

/-- Degree zero of the completed source terms is the given module itself. -/
theorem term_zero : term A B δ p M 0 = AddCommGrpCat.of M := rfl

/-- The completed source differential starts with the specified connection. -/
theorem deRhamDifferential_zero (conn : Adic A B δ p M) :
    deRhamDifferential A B δ p conn 0 = AddCommGrpCat.ofHom conn.toAddMonoidHom := rfl

/-- The de Rham complex of an integrable completed-valued connection. -/
noncomputable def deRhamComplex (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (term A B δ p M) (deRhamDifferential A B δ p conn) (fun degree ↦ by
    apply AddCommGrpCat.hom_ext
    cases degree with
    | zero => exact hconn
    | succ degree => sorry)

/-- The source de Rham complex starts with its specified complete module and connection. -/
theorem deRhamComplex_zero (conn : Adic A B δ p M)
    (hconn : IsIntegrable A B δ p conn) :
    (deRhamComplex A B δ p conn hconn).X 0 = AddCommGrpCat.of M := rfl

end Adic

end Connection

end
