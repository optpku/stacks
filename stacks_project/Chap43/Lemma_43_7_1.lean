module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.AssociatedCycle.Variety

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 43.7.1: for a flat morphism of varieties, flat pullback sends the degree-`k`
associated cycle of a coherent module with support dimension at most `k` to the degree shifted
by the canonical relative-dimension gap associated cycle of its pullback. -/
@[stacks 0AZF] #check
  (AlgebraicGeometry.Scheme.Modules.associatedCycle_pullback_of_varieties :
    ∀ {K : Type u} [Field K]
      (X Y : SchemeOverField K) [Variety X] [Variety Y]
      (f : X ⟶ Y) [Flat f.left]
      (F : Y.left.Modules) [hcoh : F.IsCoherent] (k : ℤ),
      Y.hom.closedSubschemeDeltaDimension (fun _ ↦ 0)
          (Scheme.Modules.schemeTheoreticSupport F) ≤ (k : EInt) →
        CycleGroup.flatPullback (fun _ : Spec (CommRingCat.of K) ↦ 0) X Y f
            (SchemeOverField.relativeDimensionGap X Y f) k
            (Scheme.Modules.relativeAssociatedCycle Y.hom (fun _ ↦ 0) F k) =
          Scheme.Modules.relativeAssociatedCycle
            (hF := @Scheme.Modules.pullback_isCoherent X.left Y.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (LocallyOfFiniteType.isLocallyNoetherian Y.hom) f.left F hcoh)
            X.hom (fun _ ↦ 0) ((Scheme.Modules.pullback f.left).obj F)
            (k + (SchemeOverField.relativeDimensionGap X Y f : ℤ)))
