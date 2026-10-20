module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AlgebraicMorphism
import StacksCheckRecall

/-!
# Algebraic morphisms to algebraic stacks

If a 1-morphism of stacks in groupoids over `(Sch/S)_fppf` is algebraic and
the target is an algebraic stack, then the source is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 97.8.2: Let `S` be a scheme. Let `F : X ⟶ Y` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `Y` is an algebraic stack, and `F`
is algebraic, then `X` is an algebraic stack. -/
@[stacks 05XY]
#check (AlgebraicGeometry.AlgebraicStack.of_algebraic :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [AlgebraicStack Y] (F : X ⟶ Y) [Groupoids.Hom.Algebraic F],
    AlgebraicStack X)
