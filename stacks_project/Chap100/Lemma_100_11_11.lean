module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Points
import StacksCheckRecall

/-!
# Field-valued points factor through residual gerbes

If an algebraic stack `X` has a residual gerbe `ι : Z ⟶ X` at a point `x`, then
every field-valued morphism in the class of `x` factors through `ι`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

noncomputable section

universe u

/- Lemma 100.11.11: Let `X` be an algebraic stack. Let `x ∈ |X|`. Assume that
the residual gerbe of `X` at `x` exists, with inclusion `ι : Z ⟶ X`. Let
`f : Spec (.of K) ⟶ X` be a morphism where `K` is a field in the equivalence
class of `x`. Then `f` factors through `ι`. -/
@[stacks 06MW] #check
  (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factorsThrough :
    ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X}
      [IsResidualGerbe ι x] (f : FieldValuedPoint X), Points.mk f = x →
      ∃ g : GroupoidsOver.slice f.overObj ⟶ Z, Nonempty (g ≫ ι ≅ f.hom))

#check
  (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factorsThrough_iff :
    ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X}
      [IsResidualGerbe ι x] (f : FieldValuedPoint X),
      (∃ g : GroupoidsOver.slice f.overObj ⟶ Z, Nonempty (g ≫ ι ≅ f.hom)) ↔
        Points.mk f = x)
