module

public import Mathlib.RingTheory.GradedAlgebra.Basic

@[expose] public section

namespace GradedAlgebra

/-- Homogeneous multiplication on a direct-sum decomposition forces the unit into degree zero. -/
theorem one_mem_of_decomposition {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [DirectSum.Decomposition 𝒜]
    (hmul : ∀ {n m : ℕ} {x y : B}, x ∈ 𝒜 n → y ∈ 𝒜 m → x * y ∈ 𝒜 (n + m)) :
    (1 : B) ∈ 𝒜 0 := sorry

end GradedAlgebra

/-- A natural grading is an internally graded algebra when its homogeneous multiplication is given. -/
@[reducible]
def GradedAlgebra.ofNatDecomposition {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [decomposition : DirectSum.Decomposition 𝒜]
    (hmul : ∀ {n m : ℕ} {x y : B}, x ∈ 𝒜 n → y ∈ 𝒜 m → x * y ∈ 𝒜 (n + m)) :
    GradedAlgebra 𝒜 :=
  { toGradedMonoid :=
      { toGradedOne := { one_mem := GradedAlgebra.one_mem_of_decomposition 𝒜 hmul }
        toGradedMul :=
          { mul_mem := fun {i j} {gi gj} hi hj => hmul hi hj } }
    toDecomposition := decomposition }
