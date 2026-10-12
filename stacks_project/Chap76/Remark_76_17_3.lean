/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_17_2_Perturbation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Remark 76.17.3: `IsPerturbation` is the Lean rendering of `b' = θ · a'`;
its characterization states that `(a')^♯` and `(θ · a')^♯` differ by the
derivation `D` related to `θ` by Equation 76.17.1.1. -/
@[stacks 0CK6] #check (isPerturbation_iff :
    ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
      (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
      (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
      [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
      (sqA : CommSq a iX iY a')
      (θ : (Modules.pullback a).obj (Hom.relativeDifferentials sY) ⟶ Hom.conormalSheaf iX)
      (b' : X' ⟶ Y'),
      IsPerturbation sY sX' sY' iX iY a a' sqA θ b' ↔
        b' ≫ sY' = sX' ∧
          ∃ sqB : CommSq a iX iY b',
            Hom.Conormal.map sqA = Hom.Conormal.map sqB ∧
              structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
                factorizationMap sY iX iY a
                  (ofCanonicalDerivation sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))
                    (Hom.derivationOfPullback sY a θ)))
