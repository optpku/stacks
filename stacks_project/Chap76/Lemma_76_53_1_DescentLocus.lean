/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Descent locus of a finite locally free module on algebraic spaces

A morphism `g : Y' ⟶ Y` lies in the descent locus of a finite locally free
`𝒪_X`-module `E` along `f : X ⟶ Y` when `(g')^* E` is the pullback of some
finite locally free module on `Y'`. A morphism `j : Z ⟶ Y` represents that
locus when factoring through `j` is equivalent to this descent condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A morphism `g : Y' ⟶ Y` lies in the descent locus of `E` along `f` if
`(g')^* E` is isomorphic to the pullback of some finite locally free
`𝒪_{Y'}`-module. -/
def descendsAlong {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (g : Y' ⟶ Y) : Prop :=
  ∃ (N : Y'.Modules) (_ : N.IsFiniteLocallyFree),
    Nonempty
      ((AlgebraicSpace.Modules.pullback (pullback.snd f g)).obj N ≅
        (AlgebraicSpace.Modules.pullback (pullback.fst f g)).obj E)

/-- Descent along `g` is the existence of a finite locally free module on `Y'`
whose pullback along `f'` recovers the pullback of `E` along `g'`. -/
theorem descendsAlong_iff {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (g : Y' ⟶ Y) :
    descendsAlong f E g ↔
      ∃ (N : Y'.Modules) (_ : N.IsFiniteLocallyFree),
        Nonempty
          ((AlgebraicSpace.Modules.pullback (pullback.snd f g)).obj N ≅
            (AlgebraicSpace.Modules.pullback (pullback.fst f g)).obj E) :=
  sorry

/-- A morphism `j : Z ⟶ Y` represents the descent locus of `E` along `f` if,
after every base change `g : Y' ⟶ Y`, factoring through `j` is equivalent to
`E` descending along `g`. -/
def RepresentsDescentLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (j : Z ⟶ Y) : Prop :=
  ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
    Nonempty (Over.mk g ⟶ Over.mk j) ↔ descendsAlong f E g

/-- The universal property characterizing a morphism that represents the descent
locus of `E` along `f`. -/
theorem representsDescentLocus_iff {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (j : Z ⟶ Y) :
    RepresentsDescentLocus f E j ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
        Nonempty (Over.mk g ⟶ Over.mk j) ↔ descendsAlong f E g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
