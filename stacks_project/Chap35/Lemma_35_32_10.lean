/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.ElementaryShear.InvariantOpen
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineSpace

/- Lemma 35.32.10: a nonempty open of affine `n`-space, for `2 ≤ n`, invariant under every
elementary shear is either the whole space or has finite complement consisting of closed points
whose coordinates are algebraic over the positive-characteristic prime field. -/
@[stacks 0CF0]
#check
  (@AlgebraicGeometry.AffineSpace.invariantOpen_eq_top_or_finite_complement.{u} :
    ∀ {k : Type u} [Field k] (n : ℕ), 2 ≤ n →
      ∀ (W : (𝔸(ULift.{u} (Fin n); Spec (.of k))).Opens),
        (W : Set 𝔸(ULift.{u} (Fin n); Spec (.of k))).Nonempty →
        (∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ),
          (elementaryShear i j hij d).hom ⁻¹ᵁ W = W) →
        W = ⊤ ∨
          ∃ p : ℕ, p.Prime ∧ ringChar k = p ∧
            ((W : Set 𝔸(ULift.{u} (Fin n); Spec (.of k)))ᶜ).Finite ∧
            (W : Set 𝔸(ULift.{u} (Fin n); Spec (.of k)))ᶜ ⊆
              closedPoints 𝔸(ULift.{u} (Fin n); Spec (.of k)) ∧
            ∀ x : 𝔸(ULift.{u} (Fin n); Spec (.of k)), x ∉ W → ∀ i : Fin n,
              (Int.castRingHom
                ((𝔸(ULift.{u} (Fin n); Spec (.of k))).residueField x)).IsIntegralElem
                  (residueCoordinate x i))

end AlgebraicGeometry.AffineSpace
