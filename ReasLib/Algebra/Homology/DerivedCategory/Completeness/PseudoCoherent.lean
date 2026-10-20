module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent derived-complete objects

The source theorem is a consequence of the weak-Serre/cohomology-in API, but its useful reusable
surface is the direct predicate implication below.  It intentionally takes derived completeness
of the ring module as a proposition rather than rebuilding an adic-completion instance locally.

@stack 0A05
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory
namespace DerivedCategory
namespace IsPseudoCoherent

variable {A : Type u} [CommRing A]

/-- Lemma 15.92.8 (Stacks `0A05`): if the ring module `A[0]` is derived complete with respect to
`I`, then every pseudo-coherent object of `D(A)` is derived complete with respect to `I`. -/
@[stacks 0A05 "pseudo-coherent objects inherit derived completeness"]
theorem isDerivedComplete (I : Ideal A) {K : DerivedCategory (ModuleCat A)}
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I)
    (hK : CategoryTheory.DerivedCategory.IsPseudoCoherent K) :
    K.IsDerivedCompleteWithRespectTo I := sorry

end IsPseudoCoherent
end DerivedCategory
end CategoryTheory

end
