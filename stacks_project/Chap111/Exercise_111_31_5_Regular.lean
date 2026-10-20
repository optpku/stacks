/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions
public import ReasLib.AlgebraicGeometry.AffineLine.RegularFunctions

/-!
# Classical regular functions

Typed compatibility checks for the affine-space and affine-line regular-function APIs.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {k : Type u} {σ : Type v} [Field k]

#check (MvPolynomial.IsZariskiLocallyClosed :
  ∀ (Z : Set (σ → k)),
    Prop)

#check (MvPolynomial.isZariskiLocallyClosed_iff :
  ∀ (Z : Set (σ → k)),
    IsZariskiLocallyClosed Z ↔
      ∃ I J : Ideal (MvPolynomial σ k), I ≤ J ∧ Z = zeroLocus k I \ zeroLocus k J)

#check (MvPolynomial.isZariskiLocallyClosed_sdiff :
  ∀ {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J),
    IsZariskiLocallyClosed (zeroLocus k I \ zeroLocus k J))

#check (MvPolynomial.isZariskiLocallyClosed_univ :
  IsZariskiLocallyClosed (Set.univ : Set (σ → k)))

#check (MvPolynomial.IsZariskiOpenIn :
  ∀ (U Z : Set (σ → k)),
    Prop)

#check (MvPolynomial.isZariskiOpenIn_iff :
  ∀ (U Z : Set (σ → k)),
    IsZariskiOpenIn U Z ↔
      U ⊆ Z ∧ ∃ I : Ideal (MvPolynomial σ k), U = Z \ zeroLocus k I)

#check (MvPolynomial.IsRegular :
  ∀ {Z : Set (σ → k)} (φ : Z → k),
    Prop)

#check (MvPolynomial.isRegular_iff :
  ∀ {Z : Set (σ → k)} (φ : Z → k),
    IsRegular φ ↔
      ∀ z : Z, ∃ U : Set (σ → k), IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
        ∃ f g : MvPolynomial σ k,
          (∀ u ∈ U, eval u g ≠ 0) ∧
          (∀ u : Z, u.val ∈ U → φ u = eval u.val f / eval u.val g))

#check (MvPolynomial.IsPolynomial :
  ∀ {Z : Set (σ → k)} (φ : Z → k),
    Prop)

#check (MvPolynomial.isPolynomial_iff :
  ∀ {Z : Set (σ → k)} (φ : Z → k),
    IsPolynomial φ ↔ ∃ p : MvPolynomial σ k, ∀ z : Z, φ z = eval z.val p)

#check (MvPolynomial.isRegular_of_isPolynomial :
  ∀ {Z : Set (σ → k)} {φ : Z → k}
    (hφ : IsPolynomial φ),
    IsRegular φ)

#check (MvPolynomial.regularFunctions :
  ∀ (Z : Set (σ → k)),
    Subalgebra k (Z → k))

#check (MvPolynomial.mem_regularFunctions_iff :
  ∀ {Z : Set (σ → k)} {φ : Z → k},
    φ ∈ regularFunctions Z ↔ IsRegular φ)

#check (MvPolynomial.affineLinePoint :
  ∀ (x : k),
    Fin 1 → k)

#check (MvPolynomial.affineLinePoint_apply :
  ∀ (x : k) (i : Fin 1),
    affineLinePoint x i = x)

end MvPolynomial

namespace Polynomial

variable {k : Type u} [Field k]

#check (Polynomial.IsZariskiLocallyClosed :
  ∀ (Z : Set k),
    Prop)

#check (Polynomial.isZariskiLocallyClosed_iff :
  ∀ (Z : Set k),
    IsZariskiLocallyClosed Z ↔
      ∃ I J : Ideal (Polynomial k), I ≤ J ∧
        Z = {x | ∀ p ∈ I, p.eval x = 0} \ {x | ∀ p ∈ J, p.eval x = 0})

#check (Polynomial.isZariskiLocallyClosed_univ :
  IsZariskiLocallyClosed (Set.univ : Set k))

#check (Polynomial.IsZariskiOpenIn :
  ∀ (U Z : Set k),
    Prop)

#check (Polynomial.isZariskiOpenIn_iff :
  ∀ (U Z : Set k),
    IsZariskiOpenIn U Z ↔
      U ⊆ Z ∧ ∃ I : Ideal (Polynomial k), U = Z \ {x | ∀ p ∈ I, p.eval x = 0})

#check (Polynomial.IsRegular :
  ∀ {Z : Set k} (φ : Z → k),
    Prop)

#check (Polynomial.isRegular_iff :
  ∀ {Z : Set k} (φ : Z → k),
    IsRegular φ ↔
      ∀ z : Z, ∃ U : Set k, IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
        ∃ f g : Polynomial k,
          (∀ u ∈ U, g.eval u ≠ 0) ∧
          (∀ u : Z, u.val ∈ U → φ u = f.eval u.val / g.eval u.val))

#check (Polynomial.IsPolynomial :
  ∀ {Z : Set k} (φ : Z → k),
    Prop)

#check (Polynomial.isPolynomial_iff :
  ∀ {Z : Set k} (φ : Z → k),
    IsPolynomial φ ↔ ∃ p : Polynomial k, ∀ z : Z, φ z = p.eval z.val)

#check (Polynomial.isRegular_of_isPolynomial :
  ∀ {Z : Set k} {φ : Z → k}
    (hφ : IsPolynomial φ),
    IsRegular φ)

#check (Polynomial.regularFunctions :
  ∀ (Z : Set k),
    Subalgebra k (Z → k))

#check (Polynomial.mem_regularFunctions_iff :
  ∀ {Z : Set k} {φ : Z → k},
    φ ∈ regularFunctions Z ↔ IsRegular φ)

#check (Polynomial.isRegular_univ_iff_mvPolynomial :
  ∀ (φ : k → k),
    IsRegular (fun z : (Set.univ : Set k) ↦ φ z.val) ↔
      MvPolynomial.IsRegular (fun z : (Set.univ : Set (Fin 1 → k)) ↦ φ (z.val 0)))

#check (Polynomial.isPolynomial_univ_iff_mvPolynomial :
  ∀ (φ : k → k),
    IsPolynomial (fun z : (Set.univ : Set k) ↦ φ z.val) ↔
      MvPolynomial.IsPolynomial (fun z : (Set.univ : Set (Fin 1 → k)) ↦ φ (z.val 0)))

end Polynomial
