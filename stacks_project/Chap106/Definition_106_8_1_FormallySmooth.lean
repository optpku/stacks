module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap97.«97_6_0_1_Lifting»

/-!
# Formally smooth morphisms of algebraic stacks

A morphism of algebraic stacks is formally smooth when it is formally smooth
on objects as a 1-morphism of categories fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is formally smooth if it is
formally smooth on objects as a 1-morphism of categories fibred in groupoids. -/
@[mk_iff]
class FormallySmooth {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends Groupoids.Hom.FormallySmoothOnObjects f

namespace FormallySmooth

/-- The identity morphism of an algebraic stack is formally smooth. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    FormallySmooth (𝟙 X) :=
  sorry

/-- A morphism of algebraic stacks that is formally smooth on objects is
formally smooth. -/
instance of_onObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.FormallySmoothOnObjects f] : FormallySmooth f :=
  sorry

/-- A formally smooth morphism of algebraic stacks is formally smooth on
objects as a 1-morphism of categories fibred in groupoids. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FormallySmooth f] :
    Groupoids.Hom.FormallySmoothOnObjects f :=
  sorry

end FormallySmooth

end AlgebraicGeometry.AlgebraicStack
