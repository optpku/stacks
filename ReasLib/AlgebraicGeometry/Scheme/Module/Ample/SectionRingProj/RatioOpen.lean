/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.RatioOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.SectionRingProj

/-!
# Ample section-ring morphisms and ratio opens

The section-ring morphism of an ample invertible module lands in the degree-one ratio open,
where its canonical comparisons with the integral tensor powers are isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap

variable {X : Scheme.{u}} {L : X.Modules} [Invertible L] [IsAmple L]
variable {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)}

/-- The inverse image of the degree-one ratio open under an ample section-ring morphism is the
whole source scheme. -/
theorem preimage_projTwistRatioOpen_one_eq_top (hf : IsSectionRingProjMap L f) :
    f ⁻¹ᵁ projTwistRatioOpen (RingedSpace.GradedSections.grading L) 1 = ⊤ := sorry

/-- Every component of a canonical comparison for an ample section-ring morphism is an
isomorphism. -/
theorem comparison_component_isIso (hf : IsSectionRingProjMap L f)
    (P : ProjTwistPresentation (RingedSpace.GradedSections.grading L))
    (c : SectionRingProjComparison L P f) (hc : c.IsCanonical) (n : ℤ) :
    IsIso (c.component n) := sorry

end AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap
