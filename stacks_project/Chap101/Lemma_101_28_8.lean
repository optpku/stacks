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

/-!
# Gerbes are surjective, flat, and locally of finite presentation

A morphism of algebraic stacks that makes the source a gerbe over the target
is surjective, flat, and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Surjective

/-- Lemma 101.28.8 (1): Let `π : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `π` is `Surjective`. -/
@[stacks 06QI]
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Surjective f :=
  sorry

end Surjective

namespace Flat

/-- Lemma 101.28.8 (2): Let `π : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `π` is `Flat`. -/
@[stacks 06QI]
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Flat f :=
  sorry

end Flat

namespace LocallyOfFinitePresentation

/-- Lemma 101.28.8 (3): Let `π : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `π` is `LocallyOfFinitePresentation`. -/
@[stacks 06QI]
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    LocallyOfFinitePresentation f :=
  sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.AlgebraicStack
