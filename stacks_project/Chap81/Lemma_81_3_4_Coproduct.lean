module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct

/-!
# Coproduct comparison of a cocone of algebraic spaces

The canonical morphism `∐ X_i ⟶ X` induced by a cocone in `Over B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {D : J ⥤ Over B}

/-- The canonical morphism `∐ X_i ⟶ X` induced by a cocone in `Over B`. -/
def coproductToColimit [Small.{u} J] (c : Cocone D) :
    (∐ fun i : J ↦ (D.obj i).left) ⟶ c.pt.left :=
  Sigma.desc fun i ↦ (c.ι.app i).left

/-- Precomposition of `coproductToColimit c` with the `i`-th summand inclusion is the cocone
leg `X_i ⟶ X`. -/
theorem coproductToColimit_ι [Small.{u} J] (c : Cocone D) (i : J) :
    Sigma.ι (fun j : J ↦ (D.obj j).left) i ≫ coproductToColimit c = (c.ι.app i).left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
