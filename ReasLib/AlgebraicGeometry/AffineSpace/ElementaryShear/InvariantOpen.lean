/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.ElementaryShear
public import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

variable {k : Type u} [Field k] {n : ℕ}

/-- The value of an affine coordinate in the residue field of a point. -/
def residueCoordinate (x : 𝔸(ULift.{u} (Fin n); Spec (.of k))) (i : Fin n) :
    (𝔸(ULift.{u} (Fin n); Spec (.of k))).residueField x :=
  (Scheme.ΓSpecIso ((𝔸(ULift.{u} (Fin n); Spec (.of k))).residueField x)).hom
    (((𝔸(ULift.{u} (Fin n); Spec (.of k))).fromSpecResidueField x).appTop
      (coord (Spec (.of k)) (ULift.up i)))

/-- A nonempty open of affine space of dimension at least two that is invariant under every
elementary shear is either the whole space or has finite complement consisting of closed points
whose coordinates are algebraic over the positive-characteristic prime field. Coordinate
algebraicity is expressed as integrality over `ℤ` in the residue field. -/
@[stacks 0CF0]
theorem invariantOpen_eq_top_or_finite_complement (n : ℕ) (h_n : 2 ≤ n)
    (W : (𝔸(ULift.{u} (Fin n); Spec (.of k))).Opens)
    (hW : (W : Set 𝔸(ULift.{u} (Fin n); Spec (.of k))).Nonempty)
    (h_invariant : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ),
      (elementaryShear i j hij d).hom ⁻¹ᵁ W = W) :
    W = ⊤ ∨
      ∃ p : ℕ, p.Prime ∧ ringChar k = p ∧
        ((W : Set 𝔸(ULift.{u} (Fin n); Spec (.of k)))ᶜ).Finite ∧
        (W : Set 𝔸(ULift.{u} (Fin n); Spec (.of k)))ᶜ ⊆
          closedPoints 𝔸(ULift.{u} (Fin n); Spec (.of k)) ∧
        ∀ x : 𝔸(ULift.{u} (Fin n); Spec (.of k)), x ∉ W → ∀ i : Fin n,
          (Int.castRingHom ((𝔸(ULift.{u} (Fin n); Spec (.of k))).residueField x)).IsIntegralElem
            (residueCoordinate x i) := sorry

end AlgebraicGeometry.AffineSpace
