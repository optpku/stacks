/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe

/-!
# Field-valued points factor through residual gerbes

If an algebraic stack `X` has a residual gerbe `ι : Z ⟶ X` at a point `x`, then
every field-valued morphism in the class of `x` factors through `ι`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Lemma 100.11.11: Let `X` be an algebraic stack. Let `x ∈ |X|`. Assume that
the residual gerbe of `X` at `x` exists, with inclusion `ι : Z ⟶ X`. Let
`f : Spec (.of K) ⟶ X` be a morphism where `K` is a field in the equivalence
class of `x`. Then `f` factors through `ι`. -/
@[stacks 06MW]
theorem factorsThrough {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X}
    [IsResidualGerbe ι x] (f : FieldValuedPoint X) (hf : Points.mk f = x) :
    ∃ g : GroupoidsOver.slice f.overObj ⟶ Z, Nonempty (g ≫ ι ≅ f.hom) :=
  sorry

/-- A field-valued point of `X` factors through a residual gerbe at `x` if and
only if it represents `x`. -/
theorem factorsThrough_iff {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X}
    [IsResidualGerbe ι x] (f : FieldValuedPoint X) :
    (∃ g : GroupoidsOver.slice f.overObj ⟶ Z, Nonempty (g ≫ ι ≅ f.hom)) ↔
      Points.mk f = x :=
  sorry

/-- A morphism `Spec (.of K) ⟶ X` in the class of `x` factors through a residual
gerbe inclusion `ι : Z ⟶ X`. -/
theorem of_field {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X}
    [IsResidualGerbe ι x] (K : Type u) [Field K] (σ : Spec (.of K) ⟶ S)
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ X)
    (hf : Points.mk (FieldValuedPoint.of K σ f) = x) :
    ∃ g : GroupoidsOver.slice (Over.mk σ) ⟶ Z, Nonempty (g ≫ ι ≅ f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
