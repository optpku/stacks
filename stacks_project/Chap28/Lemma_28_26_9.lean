module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionRingProj
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 28.26.9: an invertible module whose positive homogeneous nonvanishing opens cover a
scheme determines a canonical morphism to the projective spectrum of its section ring,
with the basic-open, multiplicative comparison, section-identity, and local-isomorphism
properties. -/
@[stacks 01PZ]
#check (AlgebraicGeometry.Scheme.Modules.exists_sectionRingProj :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.Scheme.Modules.Invertible L],
    AlgebraicGeometry.Scheme.Modules.IsSectionRingCover L →
      ∃ f : X ⟶ AlgebraicGeometry.Proj
        (AlgebraicGeometry.RingedSpace.GradedSections.grading L),
        AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap L f)
