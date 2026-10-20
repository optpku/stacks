module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Inertia.Presentation
public import stacks_project.Chap78.Lemma_78_16_1_Stabilizer

/-!
# Stabilizer-conjugation compatibility

Typed checks preserve the construction and comparison interfaces for existing imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

universe u

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.inertiaPresentation :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
    GroupoidAlgebraicSpace B → GroupoidAlgebraicSpace B)
