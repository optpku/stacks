/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap64.Definition_64_18_6_Stalk
public import stacks_project.Chap64.Definition_64_19_3_Stalk

/-!
# Deligne conclusions for lisse Q_ℓ-sheaves

The three conclusions of Deligne's conjectures on Frobenius characteristic
polynomials of a lisse sheaf. Geometric stalks are owned by
`Definition_64_18_6_Stalk`; closed-point geometric points and residue-field
Galois action are owned by `Definition_64_19_1_FrobeniusStalk`; their inverse-limit
and scalar-extension action on `ℚ_[ℓ]`-stalks is reused from
`Definition_64_19_3_Stalk`. Compactly
supported `H_c^i` and `π_X^*` remain in `Theorem_64_20_2_Adic_sheaves_Euler`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open GrothendieckTopology.Point
open IsDedekindDomain Matrix
open scoped AlgebraicGeometry NumberField Polynomial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (F : ZEllSheaf X.left ℓ)

/-- Characteristic polynomial of geometric Frobenius on a finite-dimensional
closed-point `ℚ_[ℓ]`-stalk. -/
def geometricFrobeniusStalkCharpoly (x : closedPoints X.left)
    (hFD : FiniteDimensional ℚ_[ℓ]
      (F.qellStalk (geometricPointOverClosedPoint X x))) :
    Polynomial ℚ_[ℓ] :=
  -- Local instance justification (proof-local temporary data): `LinearMap.charpoly` needs finite-dimensionality of this closed-point stalk; `hFD` is an explicit per-stalk hypothesis and cannot be a global instance on all `ZEllSheaf` stalks.
  haveI := hFD
  LinearMap.charpoly (F.geometricFrobeniusStalk x)

/-- Unfolding of `geometricFrobeniusStalkCharpoly` as `LinearMap.charpoly` of
`π_x^*`. -/
theorem geometricFrobeniusStalkCharpoly_eq (x : closedPoints X.left)
    (hFD : FiniteDimensional ℚ_[ℓ]
      (F.qellStalk (geometricPointOverClosedPoint X x))) :
    -- Local instance justification (proof-local temporary data): the companion type mentions `LinearMap.charpoly` at the same stalk, so it needs the same explicit finite-dimensionality.
    haveI := hFD
    F.geometricFrobeniusStalkCharpoly x hFD =
      LinearMap.charpoly (F.geometricFrobeniusStalk x) := sorry

/-- Characteristic polynomial of a general-linear automorphism of `R^r`. -/
def generalLinearCharpoly {R : Type u} [Field R] {r : ℕ}
    (g : GL (Fin r) R) : R[X] :=
  LinearMap.charpoly (GeneralLinearGroup.toLin g).val

/-- Unfolding of `generalLinearCharpoly` as the characteristic polynomial of the
underlying linear automorphism. -/
theorem generalLinearCharpoly_eq {R : Type u} [Field R] {r : ℕ}
    (g : GL (Fin r) R) :
    generalLinearCharpoly g = LinearMap.charpoly (GeneralLinearGroup.toLin g).val :=
  sorry

/-- Residual characteristic of a height-one prime of the ring of integers of a
number field. -/
def residualChar {E : Type u} [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 E)) : ℕ :=
  ringChar (𝓞 E ⧸ v.asIdeal)

/-- Unfolding of residual characteristic as `ringChar` of the residue ring. -/
theorem residualChar_eq {E : Type u} [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 E)) :
    residualChar v = ringChar (𝓞 E ⧸ v.asIdeal) := sorry

variable [ConnectedSpace X.left]

/-- A `ℚ_[ℓ]`-sheaf satisfies Deligne's conclusions when there is a number field
`E` such that every closed-point geometric stalk is finite-dimensional,
geometric Frobenius characteristic polynomials at closed points have
coefficients in `E` with complex absolute value `1` on eigenvalues, and after a
finite extension `E'/E` there is a compatible continuous representation
`etaleFundamentalGroup X.left xbar →ₜ* GL (Fin r) (v.adicCompletion E')` at
every finite place `v` of residual characteristic not `p`. -/
def SatisfiesDeligneConclusions : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]),
    (∀ (x : closedPoints X.left),
        ∃ (hFD : FiniteDimensional ℚ_[ℓ]
            (F.qellStalk (geometricPointOverClosedPoint X x)))
          (p : E[X]),
          p.map σ = F.geometricFrobeniusStalkCharpoly x hFD ∧
            ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α → ‖α‖ = 1) ∧
      ∃ (E' : Type u) (_ : Field E') (_ : NumberField E')
          (ι : E →+* E') (σ' : E' →+* ℚ_[ℓ]) (r : ℕ)
          (xbar : GeometricPoint X.left),
        ι.Finite ∧ σ'.comp ι = σ ∧
          ∀ (v : HeightOneSpectrum (𝓞 E')), residualChar v ≠ p →
            ∃ (ρ : ContinuousMonoidHom (etaleFundamentalGroup X.left xbar)
                (GL (Fin r) (v.adicCompletion E'))),
              ∀ (x : closedPoints X.left),
                ∃ (hFD : FiniteDimensional ℚ_[ℓ]
                    (F.qellStalk (geometricPointOverClosedPoint X x)))
                  (g : etaleFundamentalGroup X.left xbar) (p : E'[X]),
                  p.map σ' = F.geometricFrobeniusStalkCharpoly x hFD ∧
                    p.map (NumberField.FinitePlace.embedding v) =
                      generalLinearCharpoly (ρ g)

/-- Deligne's conclusions include finite-dimensionality of every closed-point
geometric `ℚ_[ℓ]`-stalk. -/
theorem finiteDimensional_qellStalk_of_satisfiesDeligneConclusions
    (hF : F.SatisfiesDeligneConclusions) (x : closedPoints X.left) :
    FiniteDimensional ℚ_[ℓ]
      (F.qellStalk (geometricPointOverClosedPoint X x)) := sorry

/-- Deligne's conclusions split as finite-dimensional closed stalks, algebraicity
of Frobenius characteristic polynomials, unit-root eigenvalues, and a compatible
system of `E'_λ`-representations after a finite extension of `E`. -/
theorem satisfiesDeligneConclusions_iff :
    F.SatisfiesDeligneConclusions ↔
      ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]),
        (∀ (x : closedPoints X.left),
            ∃ (hFD : FiniteDimensional ℚ_[ℓ]
                (F.qellStalk (geometricPointOverClosedPoint X x)))
              (p : E[X]),
              p.map σ = F.geometricFrobeniusStalkCharpoly x hFD ∧
                ∀ (τ : E →+* ℂ) (α : ℂ), (p.map τ).IsRoot α → ‖α‖ = 1) ∧
          ∃ (E' : Type u) (_ : Field E') (_ : NumberField E')
              (ι : E →+* E') (σ' : E' →+* ℚ_[ℓ]) (r : ℕ)
              (xbar : GeometricPoint X.left),
            ι.Finite ∧ σ'.comp ι = σ ∧
              ∀ (v : HeightOneSpectrum (𝓞 E')), residualChar v ≠ p →
                ∃ (ρ : ContinuousMonoidHom (etaleFundamentalGroup X.left xbar)
                    (GL (Fin r) (v.adicCompletion E'))),
                  ∀ (x : closedPoints X.left),
                    ∃ (hFD : FiniteDimensional ℚ_[ℓ]
                        (F.qellStalk (geometricPointOverClosedPoint X x)))
                      (g : etaleFundamentalGroup X.left xbar) (p : E'[X]),
                      p.map σ' = F.geometricFrobeniusStalkCharpoly x hFD ∧
                        p.map (NumberField.FinitePlace.embedding v) =
                          generalLinearCharpoly (ρ g) :=
  sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
