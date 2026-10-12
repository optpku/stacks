/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import stacks_project.Chap64.Definition_64_19_1_EulerFactor
public import stacks_project.Chap64.Definition_64_19_1_LFunction
public import stacks_project.Chap64.Definition_64_19_3_Stalk

/-!
# L-functions of Q_ℓ-sheaves

The Euler product
`∏_{x ∈ |X|} det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`
in `ℚ_[ℓ]⟦T⟧`, assembled coefficientwise from `LinearMap.eulerFactor` of
geometric Frobenius over closed points of bounded residue degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (F : ZEllSheaf X.left ℓ)

/-- The local Euler factor `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` in `ℚ_[ℓ]⟦T⟧`. -/
def localEulerFactor (hF : F.IsConstructible) (x : closedPoints X.left) :
    PowerSeries ℚ_[ℓ] :=
  -- Local instance justification (proof-local temporary data): finite-dimensionality of a constructible Q_ℓ-stalk is a theorem from hF; LinearMap.eulerFactor needs Module.Finite/Projective, which cannot be a global instance on all ZEllSheaf.
  haveI : FiniteDimensional ℚ_[ℓ] (F.qellStalk (geometricPointOverClosedPoint X x)) :=
    F.finiteDimensional_qellStalk hF (geometricPointOverClosedPoint X x)
  LinearMap.eulerFactor (F.geometricFrobeniusStalk x) (X.hom.residueDegree x.1)

/-- The local Euler factor is `LinearMap.eulerFactor` of geometric Frobenius at
residue degree `deg x`. -/
theorem localEulerFactor_spec (hF : F.IsConstructible) (x : closedPoints X.left) :
    -- Local instance justification (proof-local temporary data): mentioning LinearMap.eulerFactor in the companion type needs the same constructible finite-dimensionality as localEulerFactor.
    haveI : FiniteDimensional ℚ_[ℓ] (F.qellStalk (geometricPointOverClosedPoint X x)) :=
      F.finiteDimensional_qellStalk hF (geometricPointOverClosedPoint X x)
    F.localEulerFactor hF x =
      LinearMap.eulerFactor (F.geometricFrobeniusStalk x) (X.hom.residueDegree x.1) :=
  sorry

/-- The constant coefficient of each local Euler factor is `1`. -/
theorem constantCoeff_localEulerFactor (hF : F.IsConstructible)
    (x : closedPoints X.left) :
    PowerSeries.constantCoeff (F.localEulerFactor hF x) = 1 := sorry

/-- The L-function of a constructible `ℚ_[ℓ]`-sheaf, as the Euler product over
closed points of the local factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`. -/
def lFunction (hF : F.IsConstructible) : PowerSeries ℚ_[ℓ] :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff n
      (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
        F.localEulerFactor hF x.1)

/-- The coefficient of `T^n` in `lFunction` is the corresponding coefficient of
the finite product of Euler factors over closed points of residue degree at
most `n`. -/
theorem lFunction_coeff (hF : F.IsConstructible) (n : ℕ) :
    PowerSeries.coeff n (F.lFunction hF) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
          F.localEulerFactor hF x.1) := sorry

/-- The L-function is the Euler product over closed points of the local
factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`, realised coefficientwise by
finite products over residue degree at most `n`. -/
theorem lFunction_spec (hF : F.IsConstructible) :
    F.lFunction hF =
      PowerSeries.mk fun n ↦
        PowerSeries.coeff n
          (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
            F.localEulerFactor hF x.1) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
