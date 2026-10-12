/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Gerbes of algebraic stacks

A morphism of algebraic stacks is a gerbe over its target when it is a gerbe
morphism of categories fibred in groupoids on the big fppf site. An algebraic
stack is a gerbe when it is a gerbe over some algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` makes `X` a gerbe over
`Y` when `f` is a gerbe morphism of categories fibred in groupoids on
`Scheme.fppfTopology.over S`. -/
@[mk_iff]
class Gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The morphism is a gerbe morphism on the big fppf site of `S`. -/
  isGerbeMorphism : IsGerbeMorphism (Scheme.fppfTopology.over S) f

namespace Gerbe

/-- The identity morphism of an algebraic stack is a gerbe over its source. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Gerbe (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is a gerbe over its target. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    Gerbe f :=
  sorry

/-- A gerbe morphism of algebraic stacks is a gerbe morphism of groupoid
fibrations on `Scheme.fppfTopology.over S`. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Gerbe f] :
    IsGerbeMorphism (Scheme.fppfTopology.over S) f :=
  sorry

/-- A gerbe morphism of groupoid fibrations on `Scheme.fppfTopology.over S` is a
gerbe morphism of algebraic stacks. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : IsGerbeMorphism (Scheme.fppfTopology.over S) f) :
    Gerbe f :=
  sorry

/-- A morphism of algebraic stacks is a gerbe over its target if and only if it
is locally essentially surjective and locally lifts fiber morphisms on
`Scheme.fppfTopology.over S`. -/
theorem iff_localConditions {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Gerbe f ↔
      LocallyEssentiallySurjective (Scheme.fppfTopology.over S) f ∧
        LocallyLifts (Scheme.fppfTopology.over S) f :=
  sorry

end Gerbe

/-- An algebraic stack `X` over `S` is a gerbe if there exists an algebraic
space `A` over `S` and a morphism `X ⟶ A.toGroupoids` making `X` a gerbe over
`A`. -/
@[mk_iff]
class IsGerbe {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- There is a gerbe morphism from `X` to the groupoid fibration of some
  algebraic space over `S`. -/
  exists_algebraicSpace :
    ∃ (A : AlgebraicSpace S) (π : X ⟶ A.toGroupoids), Gerbe π

namespace IsGerbe

/-- A gerbe algebraic stack admits a gerbe morphism to the groupoid fibration of
some algebraic space. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsGerbe X] :
    ∃ (A : AlgebraicSpace S) (π : X ⟶ A.toGroupoids), Gerbe π :=
  sorry

/-- A gerbe morphism to the groupoid fibration of an algebraic space witnesses
that the source algebraic stack is a gerbe. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {A : AlgebraicSpace S} (π : X ⟶ A.toGroupoids) [Gerbe π] :
    IsGerbe X :=
  sorry

end IsGerbe

/-- The groupoid fibration of an algebraic space is a gerbe. -/
instance instIsGerbe_ofAlgebraicSpace {S : Scheme.{u}} (A : AlgebraicSpace S) :
    IsGerbe A.toGroupoids :=
  sorry

/-- The canonical slice of a scheme over `S` is a gerbe algebraic stack. -/
instance instIsGerbe_slice {S : Scheme.{u}} (U : Over S) :
    IsGerbe (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
