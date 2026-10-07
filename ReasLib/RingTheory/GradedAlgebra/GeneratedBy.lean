module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generation by a homogeneous graded piece

This leaf owns generation of an internally graded commutative semiring over its degree-zero
piece by an arbitrary chosen homogeneous component.  It is independent of a direct-sum
decomposition, localization, and any degree-one specialization.
-/

@[expose] public section

universe u v

namespace GradedAlgebra

variable {ι : Type u} [AddMonoid ι]
variable {S : Type v} {σ : Type*}
variable [CommSemiring S] [SetLike σ S] [AddSubmonoidClass σ S]

/-- The ambient semiring is generated over the degree-zero piece by one chosen homogeneous piece.

The degree `d` is an explicit mathematical input: degree-one generation is the specialization
`GeneratedBy 𝒜 1`, rather than a separate foundational notion. -/
@[stacks 052N "generation by one graded piece"]
def GeneratedBy (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (d : ι) : Prop :=
  Algebra.adjoin (𝒜 0) (𝒜 d : Set S) = ⊤

/-- A finite family in a chosen homogeneous component witnesses `GeneratedBy`. -/
@[stacks 052N "finite generators in a chosen graded piece"]
theorem generatedBy_of_finset
    (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] {d : ι} (s : Finset S)
    (hs_top : Algebra.adjoin (𝒜 0) (s : Set S) = ⊤)
    (hs_degree : ∀ x ∈ s, x ∈ 𝒜 d) :
    GeneratedBy 𝒜 d := sorry

/-- A generated graded component has a finite family of generators when the ambient algebra is of
finite type over degree zero. -/
@[stacks 052N "finite generators in a chosen graded piece"]
theorem exists_finset_generated_by
    (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] {d : ι}
    [Algebra.FiniteType (𝒜 0) S] (hgenerated : GeneratedBy 𝒜 d) :
    ∃ s : Finset S,
      Algebra.adjoin (𝒜 0) (s : Set S) = ⊤ ∧
        ∀ x ∈ s, x ∈ 𝒜 d := sorry

/-- For a finite-type graded algebra, generation by one homogeneous component is equivalent to
the existence of a finite generating family contained in that component. -/
@[stacks 052N "finite witness characterization of graded generation"]
theorem generatedBy_iff_exists_finset
    (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] {d : ι}
    [Algebra.FiniteType (𝒜 0) S] :
    GeneratedBy 𝒜 d ↔
      ∃ s : Finset S,
        Algebra.adjoin (𝒜 0) (s : Set S) = ⊤ ∧
          ∀ x ∈ s, x ∈ 𝒜 d := sorry

end GradedAlgebra
