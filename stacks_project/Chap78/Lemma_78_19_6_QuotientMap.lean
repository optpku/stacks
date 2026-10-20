module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Restriction

/-!
# Compatibility for restriction-induced quotient maps

The restriction abbreviation and the shared quotient map remain available to
source-facing consumers through this module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The restriction of a pre-relation along a morphism over the base. -/
abbrev restrict {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) : PreRelation U' :=
  P.pullback g

end AlgebraicGeometry.AlgebraicSpace.PreRelation

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafMap :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U),
    (P.restrict g).quotientSheaf ⟶ P.quotientSheaf)
