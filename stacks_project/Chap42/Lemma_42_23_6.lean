module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_23_4
public import ReasLib.AlgebraicGeometry.Scheme.K0.CoherentSupport

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'WithSupport

/- Lemma 42.23.6: coherent pushforward along a closed immersion into a locally Noetherian
scheme induces a bijection onto the Grothendieck group of coherent modules set-theoretically
supported on its image. -/
@[stacks 0FDT] #check
  (AlgebraicGeometry.Scheme.K0'WithSupport.closedPushforward_bijective :
    ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X]
      (i : Z ⟶ X) [IsClosedImmersion i],
      Function.Bijective (AlgebraicGeometry.Scheme.K0'WithSupport.closedPushforward i))

end AlgebraicGeometry.Scheme.K0'WithSupport
