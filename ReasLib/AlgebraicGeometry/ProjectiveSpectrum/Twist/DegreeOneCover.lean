module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Twisting sheaves under a degree-one cover

When the degree-one projective basic opens cover a projective spectrum, the canonical twisting
sheaves are invertible and the canonical multiplication and shift-comparison morphisms are
isomorphisms.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

section CanonicalTwists

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- If the degree-one projective basic opens cover `Proj 𝒜`, then every canonical twisting
sheaf is invertible. -/
theorem projTwist_invertible_of_degreeOpen_one_eq_top
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) :
    Scheme.Modules.Invertible (Proj.AssociatedModule.twistingSheaf 𝒜 n) := sorry

/-- If the degree-one projective basic opens cover `Proj 𝒜`, then every standard-open-specified
multiplication morphism between canonical twisting sheaves is an isomorphism. -/
theorem projTwistMul_isIso_of_degreeOpen_one_eq_top
    (T : Proj.AssociatedModule.TwistMultiplication 𝒜)
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (a b : ℤ) :
    IsIso (T.hom a b) := sorry

/-- If the degree-one projective basic opens cover `Proj 𝒜`, then the action of a
standard-open-specified canonical twist multiplication on any module sheaf is an isomorphism. -/
theorem projSheafTwistMul_isIso_of_degreeOpen_one_eq_top
    [SymmetricCategory (Proj 𝒜).Modules]
    (T : Proj.AssociatedModule.TwistMultiplication 𝒜)
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (ℱ : (Proj 𝒜).Modules) (a b : ℤ) :
    IsIso
      (projSheafTwistMul 𝒜 (Proj.AssociatedModule.twistingSheaf 𝒜) T.hom ℱ a b) := sorry

end CanonicalTwists

namespace Proj.AssociatedModule.ShiftComparison

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- If the degree-one projective basic opens cover `Proj 𝒜`, then every
standard-open-specified comparison between an associated module sheaf twisted by a canonical
twisting sheaf and the associated sheaf of the shifted grading is an isomorphism. -/
theorem isIso_of_degreeOpen_one_eq_top
    (C : Proj.AssociatedModule.ShiftComparison 𝒜 ℳ)
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) :
    IsIso (C.hom n) := sorry

end Proj.AssociatedModule.ShiftComparison

end AlgebraicGeometry
