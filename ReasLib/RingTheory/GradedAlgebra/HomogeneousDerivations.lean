module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.FiniteType

@[expose] public section

universe u

section HomogeneousDerivations

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

namespace Derivation

/-- A derivation is homogeneous of degree 0 when it preserves every homogeneous piece. -/
def IsHomogeneous (𝒜 : ℕ → Submodule k A) (D : Derivation k A A) : Prop :=
  ∀ d x, x ∈ 𝒜 d → D x ∈ 𝒜 d

end Derivation

namespace GradedAlgebra

/-- Homogeneous degree-0 `k`-derivations of an internally graded algebra, as a `k`-submodule of
all `k`-derivations. -/
def homogeneousDerivations (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] :
    Submodule k (Derivation k A A) where
  carrier := {D | D.IsHomogeneous 𝒜}
  add_mem' := fun hleft hright degree value hvalue ↦
    (𝒜 degree).add_mem (hleft degree value hvalue) (hright degree value hvalue)
  zero_mem' := fun degree _ _ ↦ (𝒜 degree).zero_mem
  smul_mem' := fun scalar _ hderivation degree value hvalue ↦
    (𝒜 degree).smul_mem scalar (hderivation degree value hvalue)

/-- Membership in `homogeneousDerivations` is degree-0 homogeneity. -/
theorem mem_homogeneousDerivations (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    {D : Derivation k A A} :
    D ∈ homogeneousDerivations 𝒜 ↔ D.IsHomogeneous 𝒜 := Iff.rfl

end GradedAlgebra

end HomogeneousDerivations

namespace GradedAlgebra

/-- Degree-preserving derivations of a finite-type internally graded algebra with
finite-dimensional homogeneous pieces form a finite-dimensional vector space. -/
instance homogeneousDerivations_finiteDimensional
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    [∀ degree, FiniteDimensional k (𝒜 degree)] [Algebra.FiniteType k A] :
    FiniteDimensional k (homogeneousDerivations 𝒜) := sorry

end GradedAlgebra
