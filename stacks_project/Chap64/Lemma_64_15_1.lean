/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra
import StacksCheckRecall

@[expose] public section

open Ring
open scoped MonoidAlgebra Ring

universe u v

namespace MonoidAlgebra

/- Lemma 64.15.1. Writing `1` for the identity of `G` (source `e`), the
identity-coefficient map `Λ[G] ⟶ Λ♮` sending `x` to
`CommutatorQuotient.mk (x.coeff 1)` factors through `(Λ[G])♮`. The induced
additive map is `epsilon : (Λ[G])♮ →+ Λ♮`. -/
@[stacks 03U5] #check (MonoidAlgebra.epsilon_mk :
  ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G] [Finite G] (x : Λ[G]),
    MonoidAlgebra.epsilon (Ring.CommutatorQuotient.mk x) =
      Ring.CommutatorQuotient.mk (x.coeff 1))

#check (MonoidAlgebra.epsilon_unique :
  ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G]
    (φ : (Λ[G])♮ →+ Λ♮),
    (∀ x, φ (Ring.CommutatorQuotient.mk x) =
      Ring.CommutatorQuotient.mk (x.coeff 1)) → φ = MonoidAlgebra.epsilon)

end MonoidAlgebra
