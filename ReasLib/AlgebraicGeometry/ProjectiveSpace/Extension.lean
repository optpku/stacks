/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.RatFunc.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Every morphism from `Spec (RatFunc k)` to projective `n`-space over a field `k`
that lies over `Spec k` extends to a morphism from `Spec (Polynomial k)` over `Spec k`
along the canonical inclusion of polynomials into rational functions. -/
@[stacks 0DJ2]
theorem exists_hom_fromPolynomial {k : Type u} [Field k] {n : ℕ}
    (φ : Spec (CommRingCat.of (RatFunc k)) ⟶ scheme k n)
    (h_over : φ ≫ toSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k)))) :
    ∃ ψ : Spec (CommRingCat.of (Polynomial k)) ⟶ scheme k n,
      ψ ≫ toSpec k n =
          Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ∧
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (RatFunc k))) ≫
            ψ = φ := sorry

end AlgebraicGeometry.ProjectiveSpace
