module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField

/-!
# Groupoids in algebraic spaces on a field

This module retains a typed compatibility check for the field-object predicate
while preserving the source-facing Chapter 65 and Chapter 78 prerequisite imports.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- The shared field-object predicate retains its base, groupoid, and field parameters. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.IsOnField :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k], (Spec (.of k) ⟶ S) → Prop)
