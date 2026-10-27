/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TrivialQuotient

/-!
# Gerbes with a section

A gerbe of algebraic stacks that admits a section is canonically equivalent
to the quotient stack of the trivial action of the automorphism group of that
section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicStack.RelativeIsom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {U : AlgebraicSpace S} (π : X ⟶ U.toGroupoids)
variable (x : U.toGroupoids ⟶ X)

/-- For an algebraic-stack gerbe over an algebraic space with a section, the canonical morphism
from the trivial-action quotient by the automorphism group of the section is an equivalence. -/
instance instXCanIsEquivalence [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    (toBasedFunctor (xCan π x hx)).IsEquivalence := sorry

/-- The automorphism group of a section of an algebraic-stack gerbe is flat over the base
algebraic space. -/
theorem flat_autGroup_hom [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicSpace.Flat (autGroup x).X.hom := sorry

/-- The automorphism group of a section of an algebraic-stack gerbe is locally of finite
presentation over the base algebraic space. -/
theorem locallyOfFinitePresentation_autGroup_hom [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicSpace.LocallyOfFinitePresentation (autGroup x).X.hom := sorry

/-- A section of an algebraic-stack gerbe over an algebraic space is surjective. -/
theorem surjective_section [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicStack.Surjective x := sorry

/-- A section of an algebraic-stack gerbe over an algebraic space is flat. -/
theorem flat_section [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicStack.Flat x := sorry

/-- A section of an algebraic-stack gerbe over an algebraic space is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_section [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicStack.LocallyOfFinitePresentation x := sorry

end AlgebraicGeometry.AlgebraicStack
