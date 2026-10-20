module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair

/-!
# Separated étale morphisms from a separated scheme

An étale morphism from a separated scheme to an algebraic space is representably
separated, and its represented kernel pair is a separated scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- An étale morphism from an absolutely separated scheme to an algebraic space
over a scheme is representably separated. -/
theorem isSeparated_of_etale [Scheme.IsSeparated U.left] (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf φ :=
  sorry

/-- The represented kernel pair of an étale morphism from an absolutely separated
scheme to an algebraic space is an absolutely separated scheme. -/
instance isSeparated_kernelPair [Scheme.IsSeparated U.left] (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    Scheme.IsSeparated (kernelPair φ hφ.rep).left.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
