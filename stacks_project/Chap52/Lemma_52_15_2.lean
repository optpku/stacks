/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfold `Scheme.Opens.toScheme` so typeclass search finds the canonical Noetherian open-restriction instance.
attribute [local reducible] AlgebraicGeometry.Scheme.Opens.toScheme

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}} [IsNoetherian X]

/- Lemma 52.15.2 -/
@[stacks 0EK2]
#check (AlgebraicGeometry.Scheme.CoherentCompletion.quasiAffine_implies_hasAmple_neighborhoodCompletion :
  ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
    X.IsQuasiAffine →
      Function.Bijective
        (neighborhoodComparison I (SheafOfModules.unit X.ringCatSheaf)) →
      ∃ L : X.Modules, Modules.isAmpleObject L ∧
        ∃ m₀ : ℕ, ∀ m ≥ m₀,
          Function.Bijective
            (neighborhoodComparison I (RingedSpace.TensorPower.sheaf L m)))

#check (AlgebraicGeometry.Scheme.CoherentCompletion.hasAmple_implies_finiteLocallyFree_neighborhoodCompletion :
  ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (L : X.Modules),
    Modules.isAmpleObject L →
      (∃ m₀ : ℕ, ∀ m ≥ m₀,
        Function.Bijective
          (neighborhoodComparison I (RingedSpace.TensorPower.sheaf L m))) →
      ∀ (V : (compactSupport I).openNhds)
        (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
        finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
          Function.Bijective (neighborhoodComparison
            (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj))

#check (AlgebraicGeometry.Scheme.CoherentCompletion.finiteLocallyFree_implies_fullyFaithful_neighborhoodCompletion :
  ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
    (∀ (V : (compactSupport I).openNhds)
      (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
        finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
          Function.Bijective (neighborhoodComparison
            (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj)) →
      NeighborhoodCompletionFullyFaithful I)

#check (AlgebraicGeometry.Scheme.CoherentCompletion.fullyFaithful_implies_finiteLocallyFree_neighborhoodCompletion :
  ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
    NeighborhoodCompletionFullyFaithful I →
      ∀ (V : (compactSupport I).openNhds)
        (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
        finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
          Function.Bijective (neighborhoodComparison
            (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj))

end AlgebraicGeometry.Scheme.CoherentCompletion
