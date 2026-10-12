/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap76.Lemma_76_42_4_Completion
import stacks_project.Chap76.Lemma_76_42_4_Hom

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 76.42.4: for a Noetherian algebraic space `X` over a scheme `S`, a
quasi-coherent ideal sheaf `I ⊂ 𝒪_X`, and coherent `𝒪_X`-modules `F` and `G`,
with `H = Hom(F, G)`, the canonical map from the inverse limit of the global
sections of `H / I ^ n H` to morphisms `system I F ⟶ system I G` in the
category of inverse systems of coherent modules (i.e. morphisms
`F^∧ ⟶ G^∧` in `Coh(X, I)`) is bijective. -/
@[stacks 08B6] #check
  (homComparison_bijective :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I] (F G : Coh X),
      Function.Bijective (homComparison I F G))
