module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy

/-!
# Fixed-degree opens of projective spectra

For a graded commutative ring, the fixed-degree open is the union of the projective basic opens
defined by all elements in one graded component.
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

variable {σ : Type v} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The open of `Proj 𝒜` obtained by taking the union of all basic opens defined by elements
of degree `d`. -/
def degreeOpen (d : ℕ) : (Proj 𝒜).Opens :=
  ⨆ (f : A) (_ : f ∈ 𝒜 d), basicOpen 𝒜 f

/-- The fixed-degree open is the supremum of the basic opens defined by elements of that degree. -/
theorem degreeOpen_eq_iSup (d : ℕ) :
    degreeOpen 𝒜 d = ⨆ (f : A) (_ : f ∈ 𝒜 d), basicOpen 𝒜 f := rfl

/-- A basic open defined by an element of degree `d` is contained in the fixed-degree open. -/
theorem basicOpen_le_degreeOpen {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) :
    basicOpen 𝒜 f ≤ degreeOpen 𝒜 d := sorry

/-- If a graded ring is generated over its degree-zero piece by its degree-one piece, then the
degree-one open is the whole projective spectrum. -/
theorem degreeOpen_one_eq_top_of_generatedBy
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    degreeOpen 𝒜 1 = ⊤ := sorry

end AlgebraicGeometry.Proj
