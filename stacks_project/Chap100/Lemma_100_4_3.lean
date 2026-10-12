/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_4_3_Comparison
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Bicategory
open AlgebraicGeometry.AlgebraicStack

open scoped Bicategory

/- Lemma 100.4.3: let `S` be a scheme. If
`P ⟶ X`, `P ⟶ Z`, `X ⟶ Y`, `Z ⟶ Y` is a 2-fibre product square of algebraic stacks over `S`
(Stacks diagram `Z ×_Y X → X` over `Z → Y`, written in mathlib cospan order `f : X ⟶ Y`,
`g : Z ⟶ Y`), then the comparison of points `|P| → |X| ×_{|Y|} |Z|` is surjective. -/
@[stacks 04XH] #check
  (Points.pullbackComparison_surjective :
    ∀ {S : Scheme.{u}} {P X Z Y : GroupoidsOver S}
      [AlgebraicStack P] [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Y]
      {fst : P ⟶ X} {snd : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
      (iso : fst ≫ f ≅ snd ≫ g) (h : (Points.cone iso).IsBilimit),
      Function.Surjective
        (Points.pullbackComparison iso h : Points P → Points.pullbackObj f g))
