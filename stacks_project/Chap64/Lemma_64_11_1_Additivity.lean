/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Support
public import stacks_project.Chap64.Lemma_64_11_1_Additivity_Perfect
public import stacks_project.Chap64.Proposition_64_10_2_Trace
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open FilteredObject
open scoped FilteredObject.Finite Ring

noncomputable section

universe u

namespace CochainComplex.IsBoundedFilteredFiniteProjective

open FilteredObject.Finite

variable {Λ : Type u} [Ring Λ]
variable {P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ}
variable [IsBoundedFilteredFiniteProjective P]

/-- The alternating trace of an endomorphism of a bounded filtered finite-projective
cochain complex equals the finsum of the traces of the induced endomorphisms of its
associated graded pieces. -/
theorem traceNatural_eq_sum_gradedPiece (f : P ⟶ P) :
    IsBoundedFiniteProjective.traceNatural
        ((Forget.cochain (ModuleCat.{u} Λ)).map f) =
      ∑ᶠ p : ℤ, IsBoundedFiniteProjective.traceNatural
        ((GradedPiece.cochain p).map f) :=
  sorry

/-- Only finitely many graded-piece traces of a bounded filtered finite-projective
cochain endomorphism are nonzero. -/
theorem traceNatural_gradedPiece_finiteSupport (f : P ⟶ P) :
    (Function.support fun p : ℤ ↦
        IsBoundedFiniteProjective.traceNatural
          ((GradedPiece.cochain p).map f)).Finite :=
  sorry

end CochainComplex.IsBoundedFilteredFiniteProjective

namespace CategoryTheory.FilteredObject
namespace FiniteDerived
namespace IsPerfect

variable {Λ : Type u} [Ring Λ]
variable [HasDerivedCategory (GradedObject ℤ (ModuleCat.{u} Λ))]
variable {K : Quotient.Category (ModuleCat.{u} Λ)}

/-- Lemma 64.11.1 (Additivity). Let `K` be a perfect object of `DF(ModuleCat Λ)` and
`f` an endomorphism of `K` in `DF`. Then `Tr(f|_K)`, the perfect-complex trace
`DerivedCategory.IsPerfect.traceNatural` of `(Forget.canonicalLift _).map f` in `Λ♮`,
equals `∑ᶠ p, Tr(f|_{gr^p K})`, the finsum of the traces of the induced maps
`(GradedPiece.canonicalLift _ p).map f` on associated graded pieces. -/
@[stacks 03TK]
theorem traceNatural_eq_sum_gradedPiece (hK : IsPerfect K) (f : End K) :
    (hK.forget).traceNatural ((Forget.canonicalLift (ModuleCat.{u} Λ)).map f) =
      ∑ᶠ p, (hK.gradedPiece p).traceNatural
        ((GradedPiece.canonicalLift (ModuleCat.{u} Λ) p).map f) :=
  sorry

/-- Only finitely many graded-piece traces of an endomorphism of a filtered-perfect
derived object are nonzero. -/
theorem traceNatural_gradedPiece_finiteSupport (hK : IsPerfect K) (f : End K) :
    (Function.support fun p : ℤ ↦
        (hK.gradedPiece p).traceNatural
          ((GradedPiece.canonicalLift (ModuleCat.{u} Λ) p).map f)).Finite :=
  sorry

end IsPerfect
end FiniteDerived
end CategoryTheory.FilteredObject
