/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap98.«98_9_3_1_Approximation»
public import stacks_project.Chap98.Lemma_98_27_4_Functor
public import stacks_project.Chap98.Lemma_98_27_12_RimSchlessinger
import Mathlib.Tactic.CrossRefAttribute

/-!
# Effectiveness of formal objects of the Artin contraction functor

In Situation 98.27.1, if `X' ⟶ S` is separated, then every formal object of
the contraction functor on locally Noetherian schemes over `S` is effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- The spectrum of a Noetherian complete local `S`-algebra is locally
Noetherian. -/
instance instIsLocallyNoetherian_toS (R : CompleteLocalSAlgebra S) :
    AlgebraicGeometry.IsLocallyNoetherian (Over.mk R.toS).left :=
  sorry

/-- Each maximal-adic truncation `Spec(R ⧸ m^{n+1})` is locally Noetherian. -/
instance instIsLocallyNoetherian_truncationToS (R : CompleteLocalSAlgebra S)
    (n : ℕ) :
    AlgebraicGeometry.IsLocallyNoetherian (Over.mk (R.truncationToS n)).left :=
  sorry

/-- The object `stageOver n` of `Over S` is locally Noetherian. -/
instance instIsLocallyNoetherian_stageOver (R : CompleteLocalSAlgebra S)
    (n : ℕ) :
    AlgebraicGeometry.IsLocallyNoetherian (R.stageOver n).left :=
  sorry

end AlgebraicGeometry.CompleteLocalSAlgebra

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.14: In Situation 98.27.1, if `X' ⟶ S` is separated, then every
formal object of `σ.functor` is effective. A compatible system on the
maximal-adic truncations `Spec(R ⧸ m^{n+1})` of a Noetherian complete local
`S`-algebra `R : CompleteLocalSAlgebra S`, whose residue field is of finite
type over `S`, is the restriction of a value on `Spec(R)`. The index `n : ℕ`
covers Stacks' stages `n ≥ 1`. -/
@[stacks 0GI8]
theorem hasEffectiveFormalObjects (σ : ContractionSituation S)
    [Separated (toBase σ.X')] (R : CompleteLocalSAlgebra S)
    (ξ : ∀ n, σ.functor.obj
      (op (asLocallyNoetherian (Over.mk (R.truncationToS n)))))
    (hξ : ∀ n,
      σ.functor.map (op (asLocallyNoetherianMap (R.stageHom n))) (ξ (n + 1)) =
        ξ n) :
    ∃ x : σ.functor.obj (op (asLocallyNoetherian (Over.mk R.toS))),
      ∀ n, σ.functor.map (op (asLocallyNoetherianMap (R.truncationOverHom n)))
          x = ξ n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
