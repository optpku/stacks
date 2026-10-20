/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite products of etale algebras

Mathlib provides the formal-etale product criterion and the forward instance
for etale products.  This leaf adds the corresponding `Etale` equivalence,
which also records the finite-presentation side of the property.  The index
family is the reusable owner; binary products are only a specialization.
-/

universe u v w

namespace Algebra.Etale

variable {R : Type u} {I : Type v} {A : I → Type w}
variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

/-- Finite products of etale algebras (Stacks 00U2, clause (11)): a finite
product is etale over `R` exactly when each factor is etale over `R`. -/
@[stacks 00U2 "finite products of etale algebras"]
theorem pi_iff [Finite I] :
    Algebra.Etale R (∀ i, A i) ↔ ∀ i, Algebra.Etale R (A i) := sorry

end Algebra.Etale
