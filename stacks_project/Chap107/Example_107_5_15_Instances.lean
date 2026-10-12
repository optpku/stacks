/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Definition_107_5_14_PseudoCatenary
public import stacks_project.Chap107.Situation_107_2_1_Instances

/-!
# Pseudo-catenary algebraic stacks locally of finite type over a scheme

An algebraic stack locally of finite type over a universally catenary scheme is
pseudo-catenary: any smooth scheme atlas is locally of finite type over the base,
hence universally catenary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack locally of finite type over a universally catenary scheme is
pseudo-catenary. -/
instance instIsPseudoCatenary_of_locallyOfFiniteType {S : Scheme.{u}}
    [AlgebraicGeometry.UniversallyCatenary S] (X : GroupoidsOver S)
    [AlgebraicStack X]
    [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)] :
    IsPseudoCatenary X :=
  sorry

/-- A smooth scheme atlas of an algebraic stack locally of finite type over `S`
has structure morphism locally of finite type. -/
theorem locallyOfFiniteType_hom_of_smooth {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    AlgebraicGeometry.LocallyOfFiniteType U.hom :=
  sorry

/-- A smooth scheme atlas of an algebraic stack locally of finite type over a
universally catenary scheme is itself universally catenary, by Morphisms
Lemma 29.17.2. -/
theorem universallyCatenary_of_smooth {S : Scheme.{u}}
    [AlgebraicGeometry.UniversallyCatenary S] {X : GroupoidsOver S}
    [AlgebraicStack X] [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    AlgebraicGeometry.UniversallyCatenary U.left :=
  sorry

end AlgebraicGeometry.AlgebraicStack
