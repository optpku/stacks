module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Connection

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {M : Type v} [AddCommGroup M] [Module B M]
variable {d : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}

/-- Multiplication by a scalar on each term of the de Rham complex of a connection. -/
def deRhamScalarComponent (conn : Connection d M) (a : B) :
    ∀ n, deRhamTerm conn n ⟶ deRhamTerm conn n
  | 0 => AddCommGrpCat.ofHom (LinearMap.lsmul B M a).toAddMonoidHom
  | degree + 1 =>
      AddCommGrpCat.ofHom
        (TensorProduct.map (LinearMap.lsmul B M a)
          (LinearMap.id : exteriorPower.form B Ω (degree + 1) →ₗ[B]
            exteriorPower.form B Ω (degree + 1))).toAddMonoidHom

/-- Multiplication by a horizontal scalar commutes with the de Rham differential. -/
theorem deRhamScalarComponent_comm (conn : Connection d M) (C : ExteriorCalculus d δ)
    (hconn : IsIntegrable conn C) (a : B) (h_da : d a = 0) (degree : ℕ) :
    deRhamScalarComponent conn a degree ≫ (deRhamComplex conn C hconn).d degree (degree + 1) =
      (deRhamComplex conn C hconn).d degree (degree + 1) ≫
        deRhamScalarComponent conn a (degree + 1) := sorry

/-- A horizontal scalar acts by a morphism of the de Rham complex of an integrable connection. -/
noncomputable def deRhamScalar {C : ExteriorCalculus d δ} {conn : Connection d M}
    (hconn : IsIntegrable conn C) (a : B) (h_da : d a = 0) :
    deRhamComplex conn C hconn ⟶ deRhamComplex conn C hconn :=
  CochainComplex.ofHom (deRhamScalarComponent conn a)
    (deRhamScalarComponent_comm conn C hconn a h_da)

end Connection
