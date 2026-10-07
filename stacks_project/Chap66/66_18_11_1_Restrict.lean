module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap66.Definition_66_18_1_Site

/-!
# Weak sheafification on the small étale topology

Type-valued sheaves on the small étale site of an algebraic space admit weak
sheafification, which is the existence hypothesis for cocontinuous inverse image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Type-valued weak sheafification exists on the small étale topology of an algebraic space. -/
instance smallEtaleTopology_hasWeakSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) (Type u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
