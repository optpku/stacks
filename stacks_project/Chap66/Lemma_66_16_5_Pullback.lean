module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Base change of étale morphisms of algebraic spaces

Étale morphisms of algebraic spaces are stable under arbitrary base change.
This module retains the source-facing name for base-change stability.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- Étale morphisms of algebraic spaces over `S` are stable under arbitrary
base change. -/
abbrev instIsStableUnderBaseChange {S : Scheme.{u}} :
    IsStableUnderBaseChange (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  AlgebraicGeometry.AlgebraicSpace.instIsStableUnderBaseChange_etale

#check (AlgebraicGeometry.AlgebraicSpace.Etale.instIsStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.Etale S :
      MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace.Etale
