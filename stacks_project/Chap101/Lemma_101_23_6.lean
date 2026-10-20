module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiDM.Cover

/-!
# Covering characterizations of quasi-DM morphisms of algebraic stacks

A morphism of algebraic stacks is quasi-DM if and only if every algebraic-space
test of the target has a locally quasi-finite flat algebraic-space cover of the
2-fibre product, and if and only if some fppf algebraic-space cover of the
target has such a cover of the 2-fibre product.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.23.6: a morphism is quasi-DM if and only if every algebraic-space
test of its target admits a locally quasi-finite flat algebraic-space cover
of the 2-fibre product. -/
@[stacks 06UE] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiDM.iff_existsCoverOnPullbacks :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicStack.QuasiDM f ↔
        AlgebraicGeometry.AlgebraicStack.QuasiDM.existsCoverOnPullbacks f)

/- Lemma 101.23.6: a morphism is quasi-DM if and only if some fppf
algebraic-space cover of its target admits a locally quasi-finite flat
algebraic-space cover of the 2-fibre product. -/
@[stacks 06UE] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiDM.iff_existsCoverOverFppf :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicStack.QuasiDM f ↔
        AlgebraicGeometry.AlgebraicStack.QuasiDM.existsCoverOverFppf f)
