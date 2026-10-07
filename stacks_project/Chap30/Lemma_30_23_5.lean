module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Hom
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 30.23.5: for a Noetherian scheme `X`, an ideal sheaf `I`, and coherent modules
`F` and `G`, the canonical map from the inverse limit of the global sections of
`Hom(G, F) / I ^ n Hom(G, F)` to morphisms from the completion of `G` to the completion of
`F` is bijective. -/
@[stacks 0882] #check
  (Scheme.CoherentCompletion.homComparison_bijective :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
      (F G : RingedSpace.Coh X.toRingedSpace),
      Function.Bijective (Scheme.CoherentCompletion.homComparison F G))
