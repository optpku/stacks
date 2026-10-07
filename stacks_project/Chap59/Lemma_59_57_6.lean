module

import StacksCheckRecall
import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology.Profinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-
Lemma 59.57.6 (1): for a profinite group and a discrete continuous integral `G`-module,
every positive-degree continuous group cohomology module is torsion.
-/
@[stacks 0DV3] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.profiniteGroupCohomology_isTorsion :
    ∀ (G : ProfiniteGrp) (M : CategoryTheory.Action.ModuleCat.DiscreteModuleCat ℤ G)
      (i : ℕ), 0 < i →
        Module.IsTorsion ℤ
          ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.cohomologyFunctor ℤ G i).obj M))

/-
Lemma 59.57.6 (2): if the discrete continuous coefficients form a `ℚ`-vector space, then
positive-degree continuous group cohomology vanishes.
-/
@[stacks 0DV3] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.profiniteGroupCohomology_isZero_of_rationalVector :
    ∀ (G : ProfiniteGrp) (M : CategoryTheory.Action.ModuleCat.DiscreteModuleCat ℚ G)
      (i : ℕ), 0 < i →
        IsZero ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.cohomologyFunctor ℤ G i).obj
          ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.restrictScalars
            (Int.castRingHom ℚ)).obj M)))

end
