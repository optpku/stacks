module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.Hom

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 76.42.4: for a Noetherian algebraic space `X` over a scheme `S`, a
quasi-coherent ideal sheaf `I ⊂ 𝒪_X`, and coherent `𝒪_X`-modules `F` and `G`,
with `H = Hom(F, G)`, the canonical map from the inverse limit of the global
sections of `H / I ^ n H` to morphisms `F^∧ ⟶ G^∧` in `Coh(X, I)`
is bijective. -/
@[stacks 08B6] #check
  (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.homComparison_bijective :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I] (F G : Coh X),
      Function.Bijective
        (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.homComparison I F G))

