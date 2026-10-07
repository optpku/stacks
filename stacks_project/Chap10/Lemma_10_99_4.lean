module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.RingHom.Fiber.Quotient

@[expose] public section

/-!
@stack 00MH

The source item is presented on the canonical closed-fiber owners
`Ideal.Fiber (maximalIdeal R) S` and its tensor module.  The quotient presentations are retained
in the documentation as source bridges; the two labeled conclusions below are the public API.
-/

open scoped TensorProduct Algebra.TensorProduct.Right Ideal.Fiber.Quotient

universe u v w

section CriteriaForFlatness

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

-- Local declaration justification (source-local notation): these aliases name the canonical
-- closed-fiber ring and module used verbatim in both source clauses.
local notation "ClosedFiber" => Ideal.Fiber (IsLocalRing.maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/-- Lemma 10.99.4 (1): if the closed-fiber module
`((maximalIdeal R).Fiber S) ⊗[S] M` is free over the closed-fiber ring, and `M` is flat over `R`,
then `M` is free over `S`. -/
@[stacks 00MH "(1), freeness over the target"]
theorem free_of_flat_of_free_closedFiber
    [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    Module.Free S M := sorry

/-- Lemma 10.99.4 (2): under the same closed-fiber freeness and base-flatness hypotheses, with a
nontrivial module, the local algebra map `R → S` is flat. -/
@[stacks 00MH "(2), flatness of the local map"]
theorem algebraMap_flat_of_nontrivial_flat_module_of_free_closedFiber
    [Nontrivial M] [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    (algebraMap R S).Flat := sorry

end CriteriaForFlatness

#check @free_of_flat_of_free_closedFiber
#check @algebraMap_flat_of_nontrivial_flat_module_of_free_closedFiber
