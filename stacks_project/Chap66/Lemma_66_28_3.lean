module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Faithfulness
import StacksCheckRecall

/-!
# Recovering morphisms of algebraic spaces from small étale ringed topoi

Two morphisms of algebraic spaces over a scheme that become `2`-isomorphic as morphisms of
small étale ringed topoi are equal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.28.3: let `S` be a scheme. Let `X`, `Y` be algebraic spaces over `S`. Any two
morphisms `a, b : X ⟶ Y` of algebraic spaces over `S` for which there exists a `2`-isomorphism
`(a_small, a^♯) ≅ (b_small, b^♯)` in the `2`-category of ringed topoi are equal. Here
`(a_small, a^♯)` is `ringedToposHom a`, with `a_small = (ringedToposHom a).toTopos` and
`a^♯ = (ringedToposHom a).structureMap`. -/
@[stacks 04M6]
#check (AlgebraicGeometry.AlgebraicSpace.eq_of_smallEtaleRingedTopos_twoIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {a b : X ⟶ Y},
    Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      (ringedToposHom a) (ringedToposHom b)) → a = b)

end AlgebraicGeometry.AlgebraicSpace
