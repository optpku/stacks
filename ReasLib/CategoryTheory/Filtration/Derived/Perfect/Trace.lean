module

public import ReasLib.CategoryTheory.Filtration.Derived.Perfect
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteProjective.Trace
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace

/-!
# Trace additivity for filtered-perfect derived objects

The underlying perfect-complex trace is the finitely supported sum of the
associated-graded traces in the additive commutator quotient.
-/

@[expose] public section

open CategoryTheory
open FilteredObject
open scoped FilteredObject.Finite Ring

noncomputable section

universe u

namespace CategoryTheory.FilteredObject
namespace FiniteDerived
namespace IsPerfect

variable {Λ : Type u} [Ring Λ]
variable [HasDerivedCategory (GradedObject ℤ (ModuleCat.{u} Λ))]
variable {K : Quotient.Category (ModuleCat.{u} Λ)}

/-- The trace of an endomorphism of a filtered-perfect derived object equals the
finsum of the traces induced on its associated graded pieces, with values in the
additive commutator quotient of the coefficient ring. -/
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
