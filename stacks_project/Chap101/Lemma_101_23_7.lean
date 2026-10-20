module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.Cover

/-!
# Covering characterizations of locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks is locally quasi-finite if and only if it is
quasi-DM and locally quasi-finite algebraic-space maps into 2-fibre products
remain locally quasi-finite after composing to the test space, if and only if
every algebraic-space test of the target has such a cover of the 2-fibre
product, and if and only if some fppf algebraic-space cover of the target has
such a cover of the 2-fibre product.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 101.23.7: a morphism of algebraic stacks is locally quasi-finite
if and only if it is quasi-DM and preserves locally quasi-finite
algebraic-space maps into every algebraic-space pullback; equivalently,
every such pullback admits a surjective, flat, locally finitely presented,
locally quasi-finite algebraic-space cover with locally quasi-finite
composite; equivalently, such a cover exists after one surjective, flat,
locally finitely presented algebraic-space cover of the target. -/
@[stacks 06UF] #check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE [AlgebraicStack.LocallyQuasiFinite f,
      AlgebraicStack.QuasiDM f ∧ AlgebraicStack.LocallyQuasiFinite.forallSpaceMaps f,
      AlgebraicStack.LocallyQuasiFinite.existsCoverOnPullbacks f,
      AlgebraicStack.LocallyQuasiFinite.existsCoverOverFppf f])
