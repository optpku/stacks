module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

@[expose] public section

namespace Ideal

/-- An ideal is homogeneous exactly when it is spanned by a set of homogeneous elements. -/
theorem isHomogeneous_iff_exists_homogeneous_span {ι σ R : Type*} [Semiring R]
    [SetLike σ R] [AddSubmonoidClass σ R] [DecidableEq ι] [AddMonoid ι] (grading : ι → σ)
    [GradedRing grading] (ideal : Ideal R) :
    ideal.IsHomogeneous grading ↔
      ∃ generators : Set R,
        (∀ element ∈ generators, SetLike.IsHomogeneousElem grading element) ∧
          Ideal.span generators = ideal := sorry

end Ideal
