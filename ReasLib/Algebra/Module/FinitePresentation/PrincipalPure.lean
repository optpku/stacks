/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal-pure short complexes

This leaf owns the principal-purity predicate and its cyclic-quotient lifting
criterion.  The direct-summand side keeps the source's explicit inclusion and
retraction maps, so no noncanonical direct-sum decomposition is selected.

@stack 0ASM
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum

universe u v w

section

variable {R : Type u} [CommRing R]

namespace LinearMap

variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A map is principal-pure when each principal ideal commutes with its range
under the pointwise submodule operations. -/
@[stacks 0ASM "principal-pure linear map"]
def IsPrincipalPure (f : M →ₗ[R] N) : Prop :=
  ∀ r : R,
    principalIdeal r • f.range = f.range ⊓ principalIdeal r • (⊤ : Submodule R N)

end LinearMap

variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Lemma 15.125.1 (0ASM): a module is a direct summand of a direct sum of
principal quotients `R ⧸ (f)` exactly when it lifts across every principal-pure
short exact sequence. -/
@[stacks 0ASM "principal-pure lifting criterion for cyclic quotient summands"]
theorem directSummand_iff_surjective_compRight_of_principalPure_shortExact :
    (∃ (ι : Type (max u v w)) (r : ι → R)
      (i : P →ₗ[R] (⨁ j : ι, R ⧸ principalIdeal (r j)))
      (s : (⨁ j : ι, R ⧸ principalIdeal (r j)) →ₗ[R] P),
      s.comp i = LinearMap.id) ↔
      ∀ ⦃S : ShortComplex (ModuleCat.{max u v} R)⦄
        (hS : S.ShortExact)
        (hi : LinearMap.IsPrincipalPure S.f.hom),
        Function.Surjective
          (LinearMap.compRight R S.g.hom :
            (P →ₗ[R] S.X₂) →ₗ[R] (P →ₗ[R] S.X₃)) := sorry
-- Proof strategy: for the forward implication, lift maps from each principal
-- quotient across `S.g` using principal purity, assemble the coordinate lifts
-- with `DirectSum.lift`, and pass to the retract.  Conversely, use the direct
-- sum indexed by pairs `(r, x)` with `r • x = 0` and its evaluation onto `P`;
-- its kernel inclusion is principal-pure, so the assumed surjectivity supplies
-- a section of the evaluation map.

end
