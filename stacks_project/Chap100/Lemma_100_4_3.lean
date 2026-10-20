module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Pullback
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
  (AlgebraicGeometry.AlgebraicStack.Points.pullbackComparison_surjective :
    ∀ {S : Scheme.{u}} {P X Z Y : GroupoidsOver S}
      [AlgebraicStack P] [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Y]
      {fst : P ⟶ X} {snd : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
      (iso : fst ≫ f ≅ snd ≫ g) (h : (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit),
      Function.Surjective
        (Points.pullbackComparison iso : Points P → Points.pullbackObj f g))
