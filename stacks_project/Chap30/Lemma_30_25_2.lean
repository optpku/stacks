module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.Thickening
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open Scheme.IdealSheafData

noncomputable section

universe u

/- Lemma 30.25.2: Let `X` be a Noetherian scheme with ideal sheaves `I` and `K`. If
completion is an equivalence on every positive-power `K`-thickening and a coherent formal
module admits an approximation whose stagewise kernel and cokernel are uniformly annihilated
by a power of `K`, then it lies in the essential image of completion. -/
@[stacks 088A] #check
  (Scheme.CoherentCompletion.mem_essImage_of_thickening_equivalences_and_torsion_approximation :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I K : X.IdealSheafData},
      (∀ e : ℕ+,
        (Scheme.CoherentCompletion.functor
          (I.comap (K ^ (e : ℕ)).subschemeι)).IsEquivalence) →
      (E : Scheme.CoherentFormalModules X I) →
      (∃ H : RingedSpace.Coh X.toRingedSpace,
        ∃ alpha : E ⟶ (Scheme.CoherentCompletion.functor I).obj H,
          Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K alpha) →
      (Scheme.CoherentCompletion.functor I).essImage E)
