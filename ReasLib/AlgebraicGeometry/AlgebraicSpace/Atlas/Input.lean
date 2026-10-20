/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-! # Étale atlases of algebraic spaces

An algebraic space admits a scheme over the base whose morphism to the space is
representable étale and locally surjective for the étale topology. We fix such
an atlas and record these properties.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.AtlasInput

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The scheme over the base underlying a chosen étale atlas of an algebraic space. -/
def scheme : Over S := X.atlas.choose

/-- The morphism from the chosen atlas scheme to the algebraic space. -/
def map : ofOver (scheme X) ⟶ X := X.atlas.choose_spec.choose

/-- The chosen atlas morphism is representable étale. -/
theorem representableEtale :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (map X) :=
  X.atlas.choose_spec.choose_spec.1

/-- The chosen atlas morphism is locally surjective for the étale topology. -/
theorem locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (map X) :=
  X.atlas.choose_spec.choose_spec.2

end AlgebraicGeometry.AlgebraicSpace.AtlasInput
