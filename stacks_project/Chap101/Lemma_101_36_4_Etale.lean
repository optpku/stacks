/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap101.Definition_101_34_2_EtaleSmoothLocal

/-!
# Étale morphisms of algebraic stacks

A morphism of algebraic stacks is étale when it is DM and the
étale-smooth-local-on-source-and-target lift of étale morphisms of algebraic
spaces holds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale morphisms of algebraic spaces are étale-smooth local on the
source-and-target. -/
instance Etale.isEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget (@Etale S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is étale if it is DM and has
the étale-smooth-local-on-source-and-target lift of étale morphisms of
algebraic spaces. -/
class Etale {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends DM f where
  /-- The étale-smooth-local-on-source-and-target lift of étale holds for `f`. -/
  hasEtaleSmoothLocal :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f

/-- A morphism of algebraic stacks is étale if and only if it is DM and has
the étale-smooth-local-on-source-and-target lift of étale. -/
theorem etale_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Etale f ↔
      DM f ∧ hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f :=
  sorry

namespace Etale

/-- The identity morphism of an algebraic stack is étale. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Etale (𝟙 X) :=
  sorry

/-- An étale morphism of algebraic stacks has the
étale-smooth-local-on-source-and-target lift of étale. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Etale f] :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f :=
  sorry

end Etale

end AlgebraicGeometry.AlgebraicStack
