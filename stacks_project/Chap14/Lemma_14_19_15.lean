/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.NerveCoskeletal
import StacksCheckRecall

/-!
@stack 018E

# Lemma 14.19.15 compatibility facade

The canonical owner is the global one-coskeletality instance for `SSet.stdSimplex`. Mathlib then
supplies the `IsIso` instance for the adjunction unit, while ReasLib's generic coskeletal
truncation equivalence records the mapping property used in the source proof.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

variable (n : ℕ) (U : SSet.{u})
variable (g :
  (SSet.truncation 1).obj U ⟶
    (SSet.truncation 1).obj (Δ[n] : SSet.{u}))

/- Lemma 14.19.15 (Stacks 018E): the canonical map `Δ[n] ⟶ cosk₁ sk₁ Δ[n]` is an isomorphism. -/
@[stacks 018E]
#check (inferInstance :
  IsIso ((SimplicialObject.coskAdj 1).unit.app (Δ[n] : SSet.{u})))

/- The owner-level predicate and Mathlib's canonical comparison are available downstream. -/
#check SSet.stdSimplex.isCoskeletalOne n
#check ((Δ[n] : SSet.{u}).isoCoskOfIsCoskeletal 1)

/- The source proof's Hom-set identification is the generic mapping property of a coskeletal
target and needs no separately chosen coskeleton functor. -/
#check (SimplicialObject.IsCoskeletal.truncation.homEquiv
  (Δ[n] : SSet.{u}) 1 U :
  (U ⟶ (Δ[n] : SSet.{u})) ≃
    ((SSet.truncation 1).obj U ⟶
      (SSet.truncation 1).obj (Δ[n] : SSet.{u})))

/- The inverse sends a truncated map to its canonical right-Kan lift. -/
#check (SimplicialObject.IsCoskeletal.truncation.homEquiv.symm_apply
  (Δ[n] : SSet.{u}) 1 U g)
