module

public import stacks_project.Chap60.Remark_60_6_8_Connection
import StacksCheckRecall

@[expose] public section

universe u v

/- Remark 60.6.8: let `Ω[B⁄A] →ₗ[B] Ω` be a surjective quotient satisfying the
kernel condition of Lemma 10.132.2.  A connection on `M` for the induced
derivation extends by `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ dω`; if its degree-zero curvature
vanishes, these maps square to zero in every degree and form the de Rham complex. -/
@[stacks 07I0] #check (KaehlerDifferential.DeRham.integrableConnection_squaresToZero :
    ∀ {A : Type u} [CommRing A]
      {B : Type v} [CommRing B] [Algebra A B]
      {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
      [IsScalarTower A B Ω]
      {M : Type v} [AddCommGroup M] [Module B M],
      (π : Ω[B⁄A] →ₗ[B] Ω) → (hπ : Function.Surjective π) →
      (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A]) →
      (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ) →
      (hcondition : DifferentialOperator.DeRham.KernelCondition π δ) →
      (C : ExteriorCalculus (π.compDer (KaehlerDifferential.D A B))
        (KaehlerDifferential.DeRham.descendedFamily π hπ δ hδ hcondition)) →
      (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M) →
      Connection.IsIntegrable conn C →
      Connection.SquaresToZero conn C)
