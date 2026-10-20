/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DualNumber.FlatDeformation
public import ReasLib.RingTheory.MvPolynomial.FlatDeformation
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open MvPolynomial

/- Exercise 111.5.6 (1): if `k` is a field and `A` is a `k`-algebra, then `DualNumber A` is a
flat `DualNumber k`-algebra via `algebraMapOfAlgebra`, and `DualNumber A ⧸ (ε)` is isomorphic
to `A` as a `k`-algebra. -/
@[stacks 02CV] #check (DualNumber.algebraMapOfAlgebra_flat_specialFiber :
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
    (DualNumber.algebraMapOfAlgebra k A).toRingHom.Flat ∧
      Nonempty (DualNumber.quotEps A ≃ₐ[k] A))

/- Exercise 111.5.6 (2): if `p` is prime and
`A = (ZMod p)[x_1, …, x_6] / (x_1^p, …, x_6^p)`, then the same presentation over
`ZMod (p ^ 2)` is a flat `ZMod (p ^ 2)`-algebra whose special fibre is isomorphic to `A`. -/
@[stacks 02CV] #check (MvPolynomial.truncatedPowerAlgebra_zmodSq_flat_specialFiber :
  ∀ (p : ℕ) [Fact p.Prime],
    (algebraMap (ZMod (p ^ 2)) (truncatedPowerAlgebra (ZMod (p ^ 2)) p)).Flat ∧
      Nonempty
        (zmodSqSpecialFiber p (truncatedPowerAlgebra (ZMod (p ^ 2)) p) ≃+*
          truncatedPowerAlgebra (ZMod p) p))

/- Exercise 111.5.6 (3): there is no flat `ZMod 4`-algebra `B` whose special fibre `B / 2B`
is isomorphic to
`(ZMod 2)[x_1, …, x_6] / (x_1^2, …, x_6^2, x_1 x_2 + x_3 x_4 + x_5 x_6)`. -/
@[stacks 02CV] #check (MvPolynomial.not_exists_flat_zmodFour_algebra :
  ∀ (B : Type u) [CommRing B] [Algebra (ZMod 4) B],
    ¬((algebraMap (ZMod 4) B).Flat ∧
        Nonempty (zmodSqSpecialFiber 2 B ≃+* hyperbolicTruncatedAlgebra (ZMod 2))))
