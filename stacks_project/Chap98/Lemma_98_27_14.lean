module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.FormalEffectiveness
import StacksCheckRecall

/-!
# Effectiveness of formal objects of the Artin contraction functor

In Situation 98.27.1, if `X' ⟶ S` is separated, then every formal object of
the contraction functor on locally Noetherian schemes over `S` is effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

/- Lemma 98.27.14: In Situation 98.27.1, if `X' ⟶ S` is separated, every
formal object of the contraction functor is effective. The index `n : ℕ`
represents the positive stage `Spec(R ⧸ m^{n+1})`. -/
@[stacks 0GI8] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.hasEffectiveFormalObjects :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S) [Separated (toBase σ.X')]
      (R : CompleteLocalSAlgebra S)
      (ξ : ∀ n, σ.functor.obj
        (op (asLocallyNoetherian (Over.mk (R.truncationToS n)))))
      (hξ : ∀ n,
        σ.functor.map (op (asLocallyNoetherianMap (R.stageHom n))) (ξ (n + 1)) =
          ξ n),
      ∃ x : σ.functor.obj (op (asLocallyNoetherian (Over.mk R.toS))),
        ∀ n, σ.functor.map (op (asLocallyNoetherianMap (R.truncationOverHom n)))
            x = ξ n)

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
