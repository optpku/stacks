module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Support
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective.Trace
public import ReasLib.CategoryTheory.Filtration.Trace

/-!
# Trace additivity for filtered finite-projective complexes

Alternating traces decompose into the finitely supported sum of associated-graded traces.
-/

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

