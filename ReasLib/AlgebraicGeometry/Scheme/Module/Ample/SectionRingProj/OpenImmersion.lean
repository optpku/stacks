module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.SectionRingProj
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionRingProj.Topology

/-!
# Open immersions into projective spectra of section rings

The morphism to the projective spectrum of the section ring of an ample invertible module is an
open immersion with dense image.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap

/-- A section-ring projective morphism associated to an ample invertible module is an open
immersion. -/
theorem isOpenImmersion {X : Scheme.{u}} {L : X.Modules} [Invertible L] [IsAmple L]
    {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)}
    (hf : IsSectionRingProjMap L f) : IsOpenImmersion f := sorry

/-- A section-ring projective morphism associated to an ample invertible module is an open
immersion with dense image. -/
theorem isOpenImmersion_and_isDominant {X : Scheme.{u}} {L : X.Modules}
    [Invertible L] [IsAmple L]
    {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)}
    (hf : IsSectionRingProjMap L f) : IsOpenImmersion f ∧ IsDominant f := sorry

end AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap
