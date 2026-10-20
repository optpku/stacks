module

public import Mathlib.RingTheory.GradedAlgebra.Noetherian
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import ReasLib.RingTheory.GradedAlgebra.Irrelevant
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-one generation of internally graded semirings

This leaf specializes the neutral `GradedAlgebra.GeneratedBy` API to degree one and records the
Noetherian finite-witness result that specifically concerns nonnegatively degree-one-generated
algebras.
-/

@[expose] public section

universe u v

namespace GradedAlgebra

variable {ι : Type u} [AddMonoid ι]
variable {S : Type v} {σ : Type*}
variable [CommSemiring S] [SetLike σ S] [AddSubmonoidClass σ S]

/-- A multiplicatively graded family of additive subobjects generates its ambient commutative
semiring over the degree-zero component from the degree-one component.  Only the graded-monoid
structure is needed here; a direct-sum decomposition is not part of this predicate. -/
@[stacks 052N "degree-one generation"]
abbrev DegreeOneGenerated (𝒜 : ι → σ) [One ι] [SetLike.GradedMonoid 𝒜] : Prop :=
  GeneratedBy 𝒜 1

/-- A finite family of degree-one elements which generates the ambient semiring over its
degree-zero component witnesses degree-one generation. -/
@[stacks 052N "finite degree-one generation witness"]
theorem degreeOneGenerated_of_finset
    (𝒜 : ι → σ) [One ι] [SetLike.GradedMonoid 𝒜] (s : Finset S)
    (hs_top : Algebra.adjoin (𝒜 0) (s : Set S) = ⊤)
    (hs_degree : ∀ x ∈ s, x ∈ 𝒜 1) :
    DegreeOneGenerated 𝒜 := sorry

/-- A degree-one-generated semiring of finite type over its degree-zero component has a finite set
of degree-one algebra generators. -/
@[stacks 052N "finite degree-one generators"]
theorem exists_finset_degreeOne
    (𝒜 : ι → σ) [One ι] [SetLike.GradedMonoid 𝒜]
    [Algebra.FiniteType (𝒜 0) S] (hgenerated : DegreeOneGenerated 𝒜) :
    ∃ s : Finset S,
      Algebra.adjoin (𝒜 0) (s : Set S) = ⊤ ∧
        ∀ x ∈ s, x ∈ 𝒜 1 := sorry

/-- A Noetherian degree-one spanning hypothesis has a finite homogeneous spanning witness. -/
@[stacks 00K1 "finite degree-one spanning witness"]
theorem exists_finset_span_degreeOne_eq_irrelevant
    {R : Type*} [CommSemiring R] {S : Type v} [CommRing S] [Algebra R S]
    (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜] [IsNoetherianRing S]
    (hgen : Ideal.span (𝒜 1 : Set S) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    ∃ t : Finset S, (∀ x ∈ t, x ∈ 𝒜 1) ∧
      Ideal.span (t : Set S) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal := sorry

end GradedAlgebra
