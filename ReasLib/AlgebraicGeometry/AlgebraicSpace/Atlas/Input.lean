/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-! # The actual atlas contained in an algebraic-space input

This low-level owner has no module, small-site, meromorphic, or point-closure
dependency. It extracts only the witness already present in the input.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.AtlasInput

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

def scheme : Over S := X.atlas.choose
def map : ofOver (scheme X) ⟶ X := X.atlas.choose_spec.choose

theorem representableEtale :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (map X) :=
  X.atlas.choose_spec.choose_spec.1

theorem locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (map X) :=
  X.atlas.choose_spec.choose_spec.2

end AlgebraicGeometry.AlgebraicSpace.AtlasInput
