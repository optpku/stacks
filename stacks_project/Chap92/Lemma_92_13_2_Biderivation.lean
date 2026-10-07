module

public import stacks_project.Chap92.Definition_92_13_1_Biderivation
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.Finsupp.LSum

@[expose] public section
universe u
open MulOpposite
namespace MvPolynomial

variable (R : Type u) [CommRing R] {σ : Type u} {M : Type u}
variable [AddCommGroup M] [Module R M]
variable [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ R)ᵐᵒᵖ M]

/-- Generator values satisfy the relation needed for a Leibniz map on commuting variables. -/
def BiderivationCompatible (m : σ → M) : Prop :=
  ∀ s t, (X s : MvPolynomial σ R) • m t +
      op (X t : MvPolynomial σ R) • m s =
    (X t : MvPolynomial σ R) • m s + op (X s : MvPolynomial σ R) • m t

/-- Linear extension of the word Leibniz formula, without claiming the Leibniz law
until generator compatibility has been supplied. -/
noncomputable def mkBiderivationₗ (m : σ → M) : MvPolynomial σ R →ₗ[R] M :=
  let rec word : List σ → M
    | [] => 0
    | s :: t =>
        op (List.prod (t.map fun i ↦ (X i : MvPolynomial σ R))) • m s +
          (X s : MvPolynomial σ R) • word t
  Finsupp.lsum R
    (fun xs : σ →₀ ℕ ↦
      (LinearMap.ringLmapEquivSelf R R M).symm (word xs.toMultiset.toList)) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

variable [IsScalarTower R (MvPolynomial σ R) M]
variable [IsScalarTower R (MvPolynomial σ R)ᵐᵒᵖ M]
variable [SMulCommClass (MvPolynomial σ R) (MvPolynomial σ R)ᵐᵒᵖ M]

/-- Under the commuting-generator relation the explicit linear extension is Leibniz. -/
theorem mkBiderivationₗ_leibniz (m : σ → M) (hm : BiderivationCompatible R m)
    (x y : MvPolynomial σ R) :
    mkBiderivationₗ R m (x * y) =
      x • mkBiderivationₗ R m y + op y • mkBiderivationₗ R m x := sorry

/-- The compatible polynomial biderivation uses the explicit linear extension as its map. -/
noncomputable def mkBiderivation (m : σ → M) (hm : BiderivationCompatible R m) :
    Biderivation R (MvPolynomial σ R) M where
  toLinearMap := mkBiderivationₗ R m
  leibniz' := mkBiderivationₗ_leibniz R m hm

/-- The explicit extension realizes the assigned generator values. -/
theorem mkBiderivation_X (m : σ → M) (hm : BiderivationCompatible R m) (s : σ) :
    (mkBiderivation R m hm).toLinearMap (X s) = m s := sorry

/-- Polynomial biderivations are determined by their values on variables. -/
theorem biderivation_ext {D₁ D₂ : Biderivation R (MvPolynomial σ R) M}
    (h : ∀ s, D₁.toLinearMap (X s) = D₂.toLinearMap (X s)) : D₁ = D₂ := sorry

/-- A biderivation with the compatible prescribed values equals the explicit extension. -/
theorem eq_mkBiderivation (D : Biderivation R (MvPolynomial σ R) M) (m : σ → M)
    (hm : BiderivationCompatible R m) (h : ∀ s, D.toLinearMap (X s) = m s) :
    D = mkBiderivation R m hm := sorry

end MvPolynomial
