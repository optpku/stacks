/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- The section correspondence is with compatible target-isomorphism classes. Both directions
use explicit model data; bijectivity is not used to choose an inverse. -/
@[stacks 01OB "section quotient-class correspondence"]
noncomputable def sectionLiftEquiv
    (π : P ⟶ X) (hπ : Representation π ℰ) :
    Lift π (𝟙 X) ≃ CategoryTheory.InvertibleQuotient.IsoClass ℰ :=
  let e := CategoryTheory.InvertibleQuotient.isoClassEquivOfIso
    ((Scheme.Modules.pullbackId X).app ℰ)
  { toFun := fun σ ↦ e (hπ.liftToQuotientClass (𝟙 X) σ)
    invFun := fun q ↦ hπ.liftOfQuotientClass (𝟙 X) (e.symm q)
    left_inv := by
      intro σ
      apply hπ.liftToQuotientClass_injective (𝟙 X)
      simp only [Representation.liftOfQuotientClass_eq, Equiv.symm_apply_apply]
    right_inv := by
      intro q
      simp only [Representation.liftOfQuotientClass_eq, Equiv.apply_symm_apply] }

/-- The invertible quotient represented by a section of a projective bundle. -/
@[stacks 01OB "section quotient"]
noncomputable def sectionQuotient
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    CategoryTheory.InvertibleQuotient ℰ :=
  CategoryTheory.InvertibleQuotient.precomposeIso
    ((Scheme.Modules.pullbackId X).app ℰ).symm (hπ.liftSourceQuotient (𝟙 X) σ)

/-- The target of a section quotient is the target of its universal lift quotient. -/
@[stacks 01OB "section quotient target"]
theorem sectionQuotient_object
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    (sectionQuotient π hπ σ).object = (hπ.liftSourceQuotient (𝟙 X) σ).object := sorry

/-- The quotient morphism associated to a section is the universal lift quotient composed with the
inverse pullback-identity comparison. -/
@[stacks 01OB "section quotient morphism"]
theorem sectionQuotient_hom
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    (sectionQuotient π hπ σ).hom =
      ((Scheme.Modules.pullbackId X).app ℰ).inv ≫ (hπ.liftSourceQuotient (𝟙 X) σ).hom := sorry

/-- A section of a represented projective bundle is a closed immersion. -/
theorem section_isClosedImmersion
    (π : P ⟶ X) (hπ : Representation π ℰ)
    (σ : Lift π (𝟙 X)) :
    IsClosedImmersion σ.hom := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle
