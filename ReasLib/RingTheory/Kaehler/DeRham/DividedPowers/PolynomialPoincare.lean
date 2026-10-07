module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.BaseChange
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace DPPolynomial.DeRham

section AlgebraicComparison

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J) (ι : Type u)
variable {M : Type u} [AddCommGroup M] [Module B M]

/-- Restrict the canonical polynomial one-forms along the coefficient inclusion. -/
noncomputable instance polynomialFormModule :
    Module B (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) :=
  Module.compHom _ (algebraMap B (DPPolynomial B ι))

/-- The restricted polynomial-form action is compatible with polynomial scalars. -/
instance polynomialFormScalarTower :
    @IsScalarTower B (DPPolynomial B ι)
      (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ))
      (Algebra.toSMul : SMul B (DPPolynomial B ι))
      (inferInstance : Module (DPPolynomial B ι)
        (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ))).toSMul
      (polynomialFormModule A B δ ι).toSMul := sorry

/-- The coefficient map on canonical quotient forms, using the restricted module action. -/
noncomputable def coefficientFormMap :
    formB A B δ →ₗ[B] formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ) where
  toFun := formMap A B δ ι
  map_add' := sorry
  map_smul' := sorry

/-- The form comparison intertwines the full derivation on the polynomial extension. -/
theorem formMap_derivation (coefficient : B) :
    coefficientFormMap A B δ ι (derivationB A B δ coefficient) =
      derivationB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)
        (algebraMap B (DPPolynomial B ι) coefficient) := sorry

/-- The target connection is induced by scalar extension, not independently supplied. -/
noncomputable def inducedConnection (conn : Connection (derivationB A B δ) M) :
    Connection (derivationB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ))
      (M ⊗[B] DPPolynomial B ι) :=
  Connection.scalarExtension conn (coefficientFormMap A B δ ι) (formMap_derivation A B δ ι)

/-- The induced connection has the tensor Leibniz formula. -/
theorem inducedConnection_tmul (conn : Connection (derivationB A B δ) M)
    (element : M) (coefficient : DPPolynomial B ι) :
    (inducedConnection A B δ ι conn).toAddMonoidHom (element ⊗ₜ[B] coefficient) =
      Connection.scalarExtensionValue
        (derivationB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) conn
        (coefficientFormMap A B δ ι) element coefficient := sorry

/-- Scalar extension preserves integrability for the canonical calculi. -/
theorem inducedConnection_isIntegrable (conn : Connection (derivationB A B δ) M)
    (hconn : Connection.IsIntegrable conn (canonicalCalculus A B δ)) :
    Connection.IsIntegrable (inducedConnection A B δ ι conn)
      (canonicalCalculus A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) := sorry

/-- The scalar-extension comparison for the canonical divided-power de Rham complexes. -/
noncomputable def scalarExtensionComparison (conn : Connection (derivationB A B δ) M)
    (hconn : Connection.IsIntegrable conn (canonicalCalculus A B δ)) :
    Connection.deRhamComplex conn (canonicalCalculus A B δ) hconn ⟶
      Connection.deRhamComplex (inducedConnection A B δ ι conn)
        (canonicalCalculus A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ))
        (inducedConnection_isIntegrable A B δ ι conn hconn) :=
  { f := Connection.baseChangeDeRhamHom_f conn (canonicalCalculus A B δ) hconn
      (inducedConnection A B δ ι conn)
      (canonicalCalculus A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ))
      (inducedConnection_isIntegrable A B δ ι conn hconn) (coefficientFormMap A B δ ι)
    comm' := sorry }

/-- Degree zero is coefficient extension `m ↦ m ⊗ 1`. -/
theorem scalarExtensionComparison_zero (conn : Connection (derivationB A B δ) M)
    (hconn : Connection.IsIntegrable conn (canonicalCalculus A B δ)) :
    (scalarExtensionComparison A B δ ι conn hconn).f 0 =
      AddCommGrpCat.ofHom
        (Connection.coeffInclude : M →ₗ[B] M ⊗[B] DPPolynomial B ι).toAddMonoidHom := sorry

/-- Adjoining divided-power polynomial variables preserves the de Rham complex with coefficients. -/
theorem dpPolynomial_deRhamComparison_quasiIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u)
    {M : Type u} [AddCommGroup M] [Module B M]
    (conn : Connection (derivationB A B δ) M)
    (hconn : Connection.IsIntegrable conn (canonicalCalculus A B δ)) :
    QuasiIso (scalarExtensionComparison A B δ ι conn hconn) := sorry

end AlgebraicComparison

end DPPolynomial.DeRham

end
