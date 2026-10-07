module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.TwistedGlobalSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.QuasiCompact
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.DegreeOneCover
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization.QuasiCompact

/-!
# Twisted global sections on quasi-compact projective spectra

On a quasi-compact projective spectrum, the canonical counit from the associated sheaf of all
twisted global sections reconstructs a quasi-coherent module. Under a degree-one standard-open
cover, its induced map on every homogeneous component is the identity.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjTwistedGlobalSections

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (F : (Proj 𝒜).Modules)

/-- For a quasi-compact projective spectrum and a quasi-coherent module sheaf, the canonical
counit from the sheaf associated to all twisted global sections is an isomorphism. -/
theorem counit_isIso [CompactSpace (Proj 𝒜)] [F.IsQuasicoherent]
    (C : AlgebraicGeometry.ProjTwistedGlobalSections 𝒜 F) :
    IsIso C.counit := sorry

/-- If the degree-one projective standard opens cover the projective spectrum, every map on a
homogeneous component induced by the canonical counit is the identity. -/
theorem degreeMap_eq_id_of_degreeOpen_one_eq_top
    [CompactSpace (Proj 𝒜)] [F.IsQuasicoherent]
    (C : AlgebraicGeometry.ProjTwistedGlobalSections 𝒜 F)
    (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ) :
    C.degreeMap n = AddMonoidHom.id (degree 𝒜 F n) := sorry

end AlgebraicGeometry.ProjTwistedGlobalSections
