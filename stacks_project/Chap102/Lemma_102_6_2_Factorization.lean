/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation
public import stacks_project.Chap101.Definition_101_37_1_FiniteType

/-!
# Closed-immersion factorizations of finite type separated morphisms of algebraic stacks

A finite type separated morphism from an algebraic stack to a
quasi-compact quasi-separated algebraic space factors, over the target, through
a closed immersion into an algebraic stack whose structure morphism is separated
and of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Intermediate algebraic stack whose structure morphism to an algebraic space
`Y` is separated and of finite presentation, together with a closed immersion
from `X` filling a 2-commutative triangle over `Y`. -/
abbrev HasClosedImmersionFactorizationOfSeparatedFinitePresentation
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) : Prop :=
  ∃ (X' : GroupoidsOver S) (_ : AlgebraicStack X')
    (f' : X' ⟶ Y.toGroupoids) (_ : FinitePresentation f') (_ : Separated f')
    (i : X ⟶ X') (_ : Groupoids.Hom.ClosedImmersion i),
    Nonempty (i ≫ f' ≅ f)

/-- A finite type separated morphism from an algebraic stack to a
quasi-compact quasi-separated algebraic space factors, over the target, through
a closed immersion into an algebraic stack whose structure morphism is separated
and of finite presentation. -/
theorem exists_closedImmersion_factorization_of_finiteType_separated
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y.toGroupoids) [FiniteType f] [Separated f] :
    ∃ (X' : GroupoidsOver S) (_ : AlgebraicStack X')
      (f' : X' ⟶ Y.toGroupoids) (_ : FinitePresentation f') (_ : Separated f')
      (i : X ⟶ X') (_ : Groupoids.Hom.ClosedImmersion i),
      Nonempty (i ≫ f' ≅ f) :=
  sorry

/-- Such a morphism admits a closed-immersion factorization through a separated
finitely presented algebraic stack over the target if and only if there is an
intermediate algebraic stack, a separated finitely presented morphism to `Y`, a
closed immersion from `X`, and a 2-isomorphism filling the triangle. -/
theorem exists_closedImmersion_factorization_of_finiteType_separated_iff
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y.toGroupoids) [FiniteType f] [Separated f] :
    HasClosedImmersionFactorizationOfSeparatedFinitePresentation f ↔
      ∃ (X' : GroupoidsOver S) (_ : AlgebraicStack X')
        (f' : X' ⟶ Y.toGroupoids) (_ : FinitePresentation f') (_ : Separated f')
        (i : X ⟶ X') (_ : Groupoids.Hom.ClosedImmersion i),
        Nonempty (i ≫ f' ≅ f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
