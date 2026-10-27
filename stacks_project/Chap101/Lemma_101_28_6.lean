/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Section
import StacksCheckRecall

/-! # Gerbes with a section -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.28.6 (1): For an algebraic-stack gerbe over an algebraic space with a section, the
canonical morphism from the trivial-action quotient by the automorphism group of the section
is an equivalence. -/
@[stacks 06QG] #check (AlgebraicGeometry.AlgebraicStack.instXCanIsEquivalence :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicGeometry.AlgebraicStack X]
    {U : AlgebraicSpace S} (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    [AlgebraicGeometry.AlgebraicStack.Gerbe π] (hx : x ≫ π ≅ 𝟙 U.toGroupoids),
    (toBasedFunctor (AlgebraicGeometry.AlgebraicStack.xCan π x hx)).IsEquivalence)

/- Lemma 101.28.6 (2): The automorphism group of a section of an algebraic-stack gerbe is flat
over the base algebraic space. -/
@[stacks 06QG] #check (AlgebraicGeometry.AlgebraicStack.flat_autGroup_hom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicGeometry.AlgebraicStack X]
    {U : AlgebraicSpace S} (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    [AlgebraicGeometry.AlgebraicStack.Gerbe π] (hx : x ≫ π ≅ 𝟙 U.toGroupoids),
    AlgebraicSpace.Flat (AlgebraicGeometry.AlgebraicStack.RelativeIsom.autGroup x).X.hom)

/- Lemma 101.28.6 (3): The automorphism group of a section of an algebraic-stack gerbe is locally
of finite presentation over the base algebraic space. -/
@[stacks 06QG] #check (AlgebraicGeometry.AlgebraicStack.locallyOfFinitePresentation_autGroup_hom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicGeometry.AlgebraicStack X]
    {U : AlgebraicSpace S} (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    [AlgebraicGeometry.AlgebraicStack.Gerbe π] (hx : x ≫ π ≅ 𝟙 U.toGroupoids),
    AlgebraicSpace.LocallyOfFinitePresentation
      (AlgebraicGeometry.AlgebraicStack.RelativeIsom.autGroup x).X.hom)

/- Lemma 101.28.6 (4): A section of an algebraic-stack gerbe over an algebraic space is
surjective. -/
@[stacks 06QG] #check (AlgebraicGeometry.AlgebraicStack.surjective_section :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicGeometry.AlgebraicStack X]
    {U : AlgebraicSpace S} (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    [AlgebraicGeometry.AlgebraicStack.Gerbe π] (hx : x ≫ π ≅ 𝟙 U.toGroupoids),
    AlgebraicGeometry.AlgebraicStack.Surjective x)

/- Lemma 101.28.6 (5): A section of an algebraic-stack gerbe over an algebraic space is flat. -/
@[stacks 06QG] #check (AlgebraicGeometry.AlgebraicStack.flat_section :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicGeometry.AlgebraicStack X]
    {U : AlgebraicSpace S} (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    [AlgebraicGeometry.AlgebraicStack.Gerbe π] (hx : x ≫ π ≅ 𝟙 U.toGroupoids),
    AlgebraicGeometry.AlgebraicStack.Flat x)

/- Lemma 101.28.6 (6): A section of an algebraic-stack gerbe over an algebraic space is locally
of finite presentation. -/
@[stacks 06QG] #check (AlgebraicGeometry.AlgebraicStack.locallyOfFinitePresentation_section :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicGeometry.AlgebraicStack X]
    {U : AlgebraicSpace S} (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    [AlgebraicGeometry.AlgebraicStack.Gerbe π] (hx : x ≫ π ≅ 𝟙 U.toGroupoids),
    AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation x)
