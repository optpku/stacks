module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.Hom
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf

/-!
# Compatibility names for the restriction-of-scalars sheaf

The sheaf, its base projection, and the fibre-product comparison are supplied
by the canonical restriction-of-scalars constructions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The restriction-of-scalars fppf sheaf. -/
abbrev restrictionOfScalarsSheaf {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  RestrictionOfScalars.sheaf f g

namespace RestrictionOfScalars

/-- The structure morphism of restriction of scalars to its base sheaf. -/
abbrev toUliftSheaf {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) :
    restrictionOfScalarsSheaf f g ⟶ uliftSheaf B :=
  toBase f g

/-- The explicit fibre product is canonically isomorphic to the categorical pullback. -/
abbrev fiberIsoPullback {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) : fiber g a ≅ pullback a g :=
  fiberPullbackIso g a

end RestrictionOfScalars

end AlgebraicGeometry.AlgebraicSpace
