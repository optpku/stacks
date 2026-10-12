/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Data.Set.PowersetCard.Fin
public import ReasLib.RingTheory.Extension.Presentation.Jacobian

/-!
# Finite-coordinate views of presentation Jacobians

This leaf relates embedding-indexed Jacobian minors to the ordered-subset and
initial-coordinate notation used by finite presentations.
-/

@[expose] public section

universe u v t

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {σ : Type t} {n m c : ℕ}

/-- The Jacobian minor selected by an arbitrary relation embedding and a
canonically ordered `c`-element subset of `Fin n`. -/
@[stacks 07ER]
noncomputable def jacobianColumnMinor
    (P : Presentation R A (Fin n) σ) (rows : Fin c ↪ σ)
    (I : Set.powersetCard (Fin n) c) : P.Ring :=
  P.jacobianMinor (I.1.orderEmbOfFin I.2).toEmbedding rows

/-- The leading Jacobian determinant selected by the first `c` variables and
the first `c` relations. -/
@[stacks 07C8]
noncomputable def leadingJacobianDet
    (P : Presentation R A (Fin n) (Fin m))
    (hcₙ : c ≤ n) (hcₘ : c ≤ m) : P.Ring :=
  P.jacobianMinor (Fin.castLEEmb hcₙ) (Fin.castLEEmb hcₘ)

/-- Selecting the initial variable subset recovers the leading Jacobian
determinant. -/
theorem jacobianColumnMinor_initial
    (P : Presentation R A (Fin n) (Fin m))
    (hcₙ : c ≤ n) (hcₘ : c ≤ m) :
    P.jacobianColumnMinor (Fin.castLEEmb hcₘ) (Set.powersetCard.initial hcₙ) =
      P.leadingJacobianDet hcₙ hcₘ := sorry

namespace JacobianIdeal

/-- For variables indexed by `Fin n`, containment of an embedding-indexed
Jacobian ideal can be tested on canonically ordered variable subsets. -/
theorem le_iff_columnMinor
    (P : Presentation R A (Fin n) σ) (rows : Fin c ↪ σ) (J : Ideal A) :
    P.jacobianIdeal rows ≤ J ↔
      ∀ I : Set.powersetCard (Fin n) c,
        algebraMap P.Ring A (P.jacobianColumnMinor rows I) ∈ J := sorry

end JacobianIdeal

end Algebra.Presentation
