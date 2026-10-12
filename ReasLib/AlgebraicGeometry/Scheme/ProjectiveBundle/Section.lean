/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections

/-!
# Sections of projective bundles

This leaf specializes the universal projective-bundle quotient correspondence to the identity
morphism of the base scheme.  A representation is always an explicit argument, so the quotient
data cannot change with instance search.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {X P : Scheme.{u}} {ℰ : X.Modules}

/-- The quotient correspondence for sections of a chosen projective-bundle representation. -/
@[stacks 01OB "section quotient correspondence"]
noncomputable def sectionLiftEquiv
    (π : P ⟶ X) (hπ : Representation π ℰ) :
    Lift π (𝟙 X) ≃ CategoryTheory.InvertibleQuotient ℰ :=
  Equiv.trans (hπ.liftEquiv (𝟙 X))
    (CategoryTheory.InvertibleQuotient.equivOfIso
      ((Scheme.Modules.pullbackId X).app ℰ))

/-- The invertible quotient represented by a section of a projective bundle. -/
@[stacks 01OB "section quotient"]
noncomputable def sectionQuotient
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    CategoryTheory.InvertibleQuotient ℰ :=
  sectionLiftEquiv π hπ σ

/-- The target of a section quotient is the target of its universal lift quotient. -/
@[stacks 01OB "section quotient target"]
theorem sectionQuotient_object
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    (sectionQuotient π hπ σ).object = (hπ.liftEquiv (𝟙 X) σ).object := sorry

/-- The quotient morphism associated to a section is the universal lift quotient composed with the
inverse pullback-identity comparison. -/
@[stacks 01OB "section quotient morphism"]
theorem sectionQuotient_hom
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    (sectionQuotient π hπ σ).hom =
      ((Scheme.Modules.pullbackId X).app ℰ).inv ≫ (hπ.liftEquiv (𝟙 X) σ).hom := sorry

/-- A section of a represented projective bundle is a closed immersion. -/
theorem section_isClosedImmersion
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    IsClosedImmersion σ.hom := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle
