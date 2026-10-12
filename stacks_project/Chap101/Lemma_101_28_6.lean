/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap101.Lemma_101_28_6_Aut
public import stacks_project.Chap101.Lemma_101_28_6_Quotient

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

/-- Lemma 101.28.6 (1): if `π : X ⟶ U` is a gerbe of algebraic stacks and
`x : U ⟶ X` is a section, then the canonical 1-morphism
`xCan : [U/G] ⟶ X` from the trivial-action quotient stack of
`G = Isom_X(x, x)` is an equivalence of stacks in groupoids over
`(Sch/S)_fppf`. -/
@[stacks 06QG]
instance instXCan_isEquivalence [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    (toBasedFunctor (xCan π x hx)).IsEquivalence :=
  sorry

/-- Lemma 101.28.6 (2): if `π : X ⟶ U` is a gerbe of algebraic stacks and
`x : U ⟶ X` is a section, then `G ⟶ U` is flat, where
`G = Isom_X(x, x)`. -/
@[stacks 06QG]
theorem flat_autGroup_hom [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicSpace.Flat (autGroup x).X.hom :=
  sorry

/-- Lemma 101.28.6 (3): if `π : X ⟶ U` is a gerbe of algebraic stacks and
`x : U ⟶ X` is a section, then `G ⟶ U` is locally of finite presentation,
where `G = Isom_X(x, x)`. -/
@[stacks 06QG]
theorem locallyOfFinitePresentation_autGroup_hom [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicSpace.LocallyOfFinitePresentation (autGroup x).X.hom :=
  sorry

/-- Lemma 101.28.6 (4): if `π : X ⟶ U` is a gerbe of algebraic stacks and
`x : U ⟶ X` is a section, then `x` is surjective. -/
@[stacks 06QG]
theorem surjective_section [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicStack.Surjective x :=
  sorry

/-- Lemma 101.28.6 (5): if `π : X ⟶ U` is a gerbe of algebraic stacks and
`x : U ⟶ X` is a section, then `x` is flat. -/
@[stacks 06QG]
theorem flat_section [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicStack.Flat x :=
  sorry

/-- Lemma 101.28.6 (6): if `π : X ⟶ U` is a gerbe of algebraic stacks and
`x : U ⟶ X` is a section, then `x` is locally of finite presentation. -/
@[stacks 06QG]
theorem locallyOfFinitePresentation_section [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    AlgebraicStack.LocallyOfFinitePresentation x :=
  sorry

/-- Absolute automorphisms `Isom_X(x, x)` and relative automorphisms
`Isom_{X/U}(x, x)` represent the same group algebraic space when `x` is a
section of `π`. -/
theorem autOn_autGroup [Gerbe π]
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    Nonempty (autOn π x ≌ (autGroup x).X.left.toGroupoids) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
