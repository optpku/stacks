module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiber.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/- Lemma 68.18.4: In the cartesian square of algebraic spaces over `S` with
legs `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`, the pair-fibre
`fibre p q x z` is finite if `f` is of finite type and `f` is quasi-finite at
`x`, whenever `x` and `z` have the same image in `Points Y`. -/
@[stacks 0AC6] #check
  (AlgebraicGeometry.AlgebraicSpace.Points.fibre_finite_of_finiteType_quasiFiniteAt :
    ∀ {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
      {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y},
      IsPullback p q f g → [FiniteType f] → ∀ (x : Points X) (z : Points Z),
      QuasiFiniteAt f x → map f x = map g z → (fibre p q x z).Finite)

end AlgebraicGeometry.AlgebraicSpace.Points
