module

public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap101.Definition_101_34_2_EtaleSmoothLocal

/-!
# Unramified morphisms of algebraic stacks

A morphism of algebraic stacks is unramified when it is DM and the
étale-smooth-local-on-source-and-target lift of unramified morphisms of
algebraic spaces holds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Unramified morphisms of algebraic spaces are étale-smooth local on the
source-and-target. -/
instance Unramified.isEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget (@Unramified S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is unramified if it is DM and
has the étale-smooth-local-on-source-and-target lift of unramified morphisms of
algebraic spaces. -/
class Unramified {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends DM f where
  /-- The étale-smooth-local-on-source-and-target lift of unramified holds for
  `f`. -/
  hasEtaleSmoothLocal :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f

/-- A morphism of algebraic stacks is unramified if and only if it is DM and
has the étale-smooth-local-on-source-and-target lift of unramified. -/
theorem unramified_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Unramified f ↔
      DM f ∧
        hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f :=
  sorry

namespace Unramified

/-- The identity morphism of an algebraic stack is unramified. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Unramified (𝟙 X) :=
  sorry

/-- An unramified morphism of algebraic stacks has the
étale-smooth-local-on-source-and-target lift of unramified. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f] :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f :=
  sorry

end Unramified

end AlgebraicGeometry.AlgebraicStack
