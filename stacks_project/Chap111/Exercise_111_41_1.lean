/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_41_1_Cover
public import stacks_project.Chap111.Exercise_111_41_1_Cech
public import stacks_project.Chap111.Exercise_111_41_1_Extension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exercise 111.41.1

Čech cohomology of `𝒪` on the affine line with doubled origin, and extensions realizing each
coverwise class as `δ(1)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.DoubledOrigin CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry LaurentPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

/-- Exercise 111.41.1 (1): Let `k` be a field and let `X` be the affine line with doubled origin,
covered by `𝒰` with `U₁ = chart k 1 0 ≅ Spec k[x]` and `U₂ = chart k 1 1 ≅ Spec k[y]`, overlap
`≅ Spec k[z, 1/z]`, and both open immersions given by `x ↦ z` and `y ↦ z`. Then
`check H¹(𝒰, 𝒪)` is a `k`-vector space identified with `laurentQuotient k` by a `k`-linear
equivalence intertwining the identity glueing, and the Čech classes of `T ^ (-n)` for `n ≥ 1`
form a `k`-basis. -/
@[stacks 02F4]
theorem cechH1_basis (k : Type u) [Field k] :
    ∃ (e : Γ(scheme k 1, chartOverlap k) ≃+* LaurentPolynomial k)
      (φ : cechH1Carrier k ≃ₗ[k] laurentQuotient k),
      (∀ p : Polynomial k,
          e (leftRestriction k (chartCoordinateRingHom k 0 p)) = Polynomial.toLaurent p) ∧
      (∀ p : Polynomial k,
          e (rightRestriction k (chartCoordinateRingHom k 1 p)) = Polynomial.toLaurent p) ∧
      (∀ n : {n : ℕ // 0 < n},
          φ (cechClassOfOverlapSection k (e.symm (LaurentPolynomial.T (-(n : ℤ))))) =
            laurentQuotientMk k (LaurentPolynomial.T (-(n : ℤ)))) ∧
      Function.Bijective
        (Finsupp.linearCombination k
          (fun n : {n : ℕ // 0 < n} ↦
            cechClassOfOverlapSection k (e.symm (LaurentPolynomial.T (-(n : ℤ)))))) :=
  sorry

/-- Exercise 111.41.1 (2): For each class `c` in `check H¹(𝒰, 𝒪)` there is an exact sequence
`0 → 𝒪_X → E → 𝒪_X → 0` of sheaves of `𝒪_X`-modules whose coverwise connecting value `δ(1)` on
`𝒰` equals `c`. -/
@[stacks 02F4]
theorem exists_extension_of_cechClass (k : Type u) [Field k] (c : cechH1 k) :
    ∃ (E : (scheme k 1).toRingedSpace.Modules) (ι : unitModule k ⟶ E)
      (π : E ⟶ unitModule k) (w : ι ≫ π = 0),
      (ShortComplex.mk ι π w).ShortExact ∧ IsCoverwiseConnectingClass k ι π w c :=
  sorry

end AlgebraicGeometry.DoubledOrigin
