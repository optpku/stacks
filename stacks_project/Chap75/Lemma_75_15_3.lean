/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_15_3_Retract
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 75.15.3: on a quasi-compact quasi-separated algebraic space `X` over a
scheme `S`, every perfect object of `D(𝒪_W)` for a quasi-compact open subspace
`W ⊂ X` is a direct summand of the restriction of a perfect object of `D(𝒪_X)`. -/
@[stacks 09IX]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.exists_retract_extension_of_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (W : OpenSubspace X) [IsQuasiCompact W.X]
      (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P),
      ∃ R : ModuleDerived X,
        ModuleDerived.IsPerfect R ∧
          Nonempty (Retract P ((ModuleDerived.pullback W.ι).obj R)))
