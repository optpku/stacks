/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Open
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

/-!
# Sections of twisting sheaves on projective spectra

This module constructs sections of chosen and canonical twisting sheaves and records the
nonvanishing open of a canonical twist section after restriction to an open subscheme.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry

section Presentation

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Restrict the section of a chosen twist associated to a homogeneous element to an open
subscheme of the projective spectrum. -/
noncomputable def projTwistSectionOnOpen
    (W : (Proj 𝒜).Opens) (P : ProjTwistPresentation 𝒜) {d n : ℕ} (f : 𝒜 (n * d)) :
    Γ((Scheme.Modules.restrictFunctor W.ι).obj
      (P.actualTwist ((n : ℤ) * (d : ℤ))), ⊤) :=
  (Scheme.Modules.globalSectionsRestrict W
    (P.actualTwist ((n : ℤ) * (d : ℤ)))).hom
    ((AddCommGrpCat.Hom.hom (P.actualSectionMap (n * d))) f)

end Presentation

namespace Proj.AssociatedModule

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The canonical global section of the twisting sheaf associated to a homogeneous element. -/
noncomputable def twistSection {n : ℕ} (f : 𝒜 n) :
    Γ(twistingSheaf 𝒜 (n : ℤ), ⊤) :=
  degreeZeroToGlobalSections 𝒜
    (GradedModule.shiftGrading (DirectSum.Decomposition.natToIntGrading 𝒜) (n : ℤ))
    ⟨f, by simpa using f.2⟩

/-- Restrict the canonical twist section associated to a homogeneous element to an open
subscheme of the projective spectrum. -/
noncomputable def twistSectionOnOpen
    (W : (Proj 𝒜).Opens) {n : ℕ} (f : 𝒜 n) :
    Γ((Scheme.Modules.restrictFunctor W.ι).obj (twistingSheaf 𝒜 (n : ℤ)), ⊤) :=
  (Scheme.Modules.globalSectionsRestrict W (twistingSheaf 𝒜 (n : ℤ))).hom
    (twistSection 𝒜 f)

/-- On an open where a positive canonical twist is invertible, the nonvanishing open of the
restricted canonical section is the inverse image of its projective basic open. -/
theorem sectionNonvanishingOpen_twistSectionOnOpen
    (W : (Proj 𝒜).Opens) {n : ℕ} (hn : 0 < n) (f : 𝒜 n)
    (hL : Scheme.Modules.Invertible
      ((Scheme.Modules.restrictFunctor W.ι).obj (twistingSheaf 𝒜 (n : ℤ)))) :
    hL.sectionNonvanishingOpen (twistSectionOnOpen 𝒜 W f) =
      W.ι ⁻¹ᵁ Proj.basicOpen 𝒜 (f : A) := sorry

end Proj.AssociatedModule

end AlgebraicGeometry
