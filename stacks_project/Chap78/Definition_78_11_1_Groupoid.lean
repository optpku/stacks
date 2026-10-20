module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid

/-!
# Groupoids in algebraic spaces

This module retains typed compatibility checks for the reusable groupoid API while preserving the
source-facing Chapter 65 prerequisite imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/- The reusable groupoid owner has an algebraic-space object parameter over the current base. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace :
  (B : AlgebraicSpace S) → Type (u + 1))

/- The reusable morphism owner has two groupoids over the current base. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom :
  {B : AlgebraicSpace S} →
    AlgebraicGeometry.GroupoidAlgebraicSpace B →
      AlgebraicGeometry.GroupoidAlgebraicSpace B → Type (u + 1))

end AlgebraicGeometry
