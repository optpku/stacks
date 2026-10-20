module

import ReasLib.AlgebraicGeometry.AlgebraicStack.Limit.Separated
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry
open scoped Bicategory

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, AlgebraicSpace.IsQuasiCompact (D.obj i)]
variable [∀ i, AlgebraicSpace.IsAbsolutelyQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), AlgebraicSpace.Affine (D.map (homOfLE h))]

/- Lemma 102.4.2: In Situation 102.4.1, packaged as
`AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D`, the stages are quasi-compact
and absolutely quasi-separated, with affine transitions and no separation
assumption on the ambient scheme `S`. If `f : 𝒳0 ⟶ Y0` is a morphism from a
quasi-compact quasi-separated algebraic stack to the distinguished stage and
the limit base change `Y ×_{Y0} 𝒳0 ⟶ Y` is separated, then
`Yi ×_{Y0} 𝒳0 ⟶ Yi` is separated for every sufficiently large `i`.

Here `D.obj i` is the stage `Yi`, `s.base` is the distinguished index `0`,
`s.limitCone.cone.pt` is the limit `Y`, and the base-change morphisms are the
second 2-fibre-product projections `TwoFibreProduct.snd`. -/
@[stacks 0CPZ] #check
  (AlgebraicGeometry.AlgebraicStack.exists_eventually_separated_stage :
    ∀ (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
      {X0 : GroupoidsOver S} [AlgebraicStack X0]
      [AlgebraicStack.IsQuasiCompact X0] [AlgebraicStack.IsQuasiSeparated X0]
      (f : X0 ⟶ (D.obj s.base).toGroupoids),
      AlgebraicStack.Separated (AlgebraicStack.pullbackAlongLimit.snd s f) →
      ∃ (i : I) (hi : s.base ≤ i),
        ∀ (j : I) (hj : i ≤ j),
          AlgebraicStack.Separated (AlgebraicStack.pullbackAlongStage.snd s f j (hi.trans hj)))

end
