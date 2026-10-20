module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing

/- Remark 41.19.6: there exists a Noetherian local domain whose maximal-ideal completion is
nonreduced. -/
@[stacks 039U]
#check
  (IsAnalyticallyUnramified.exists_noetherianLocalDomain_with_nonreduced_completion :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A), ¬ IsReduced (AdicCompletion (maximalIdeal A) A))

namespace AdicCompletion

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/- The canonical map from a Noetherian local ring to its maximal-ideal completion is flat. -/
#check (RingHom.flat_algebraMap_iff.mpr
    (AdicCompletion.flat_of_isNoetherian (I := maximalIdeal A) :
      Module.Flat A (AdicCompletion (maximalIdeal A) A)) :
  (algebraMap A (AdicCompletion (maximalIdeal A) A)).Flat)

/- The extension of the source maximal ideal is the maximal ideal of the completion. -/
#check (maximalIdeal_eq_map :
  maximalIdeal (AdicCompletion (maximalIdeal A) A) =
    (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A)))

/- The canonical completion map induces a bijection on residue fields. -/
#check (residueField_map_bijective A :
  Function.Bijective (IsLocalRing.ResidueField.map
    (algebraMap A (AdicCompletion (maximalIdeal A) A))))

end AdicCompletion
