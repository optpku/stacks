module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.InfinitesimalStages

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.20.11: A locally Noetherian formal algebraic space is the
fppf-sheaf colimit of the canonical finite-order thickenings of its reduction.
Lean stage `n` is source `X_{n+1}`, cut out by the power `n + 1`. -/
@[stacks 0GHM] #check (AlgebraicGeometry.FormalAlgebraicSpace.exists_infinitesimalStages :
    ∀ {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X],
    ∃ (R : ReductionData X)
      (c : Cocone (R.infinitesimalStages ⋙ AlgebraicSpace.forgetToPresheaf))
      (hc : IsColimit c),
      (Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (hc.desc R.infinitesimalCocone) ∧
       Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
        (hc.desc R.infinitesimalCocone)) ∧
      (∀ n, AlgebraicSpace.IsLocallyNoetherian (R.infinitesimalStage n)) ∧
      (∀ (n m : ℕ) (hnm : n ≤ m),
        AlgebraicSpace.IsFiniteOrderThickening (R.stageHom hnm)) ∧
      IsIso (R.fromReduction 0) ∧
      (∀ (n m : ℕ) (hnm : n ≤ m),
        R.fromReduction 0 ≫ R.neighbourhoodFromSource m n =
            R.fromReduction n ≫ (R.infinitesimalStageIsoNeighbourhood hnm).hom ∧
          (R.infinitesimalStageIsoNeighbourhood hnm).hom ≫
            R.neighbourhoodToAmbient m n = R.stageHom hnm))
