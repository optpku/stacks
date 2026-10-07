module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.SmoothBaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 37.19.2 (Normalization commutes with smooth base change): the canonical
normalization comparison after smooth base change is an isomorphism. -/
@[stacks 03GV] #check
  (AlgebraicGeometry.Scheme.Hom.isIso_normalizationPullback_of_smooth :
    ∀ {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
      [QuasiCompact f] [QuasiSeparated f] [Smooth g],
      IsIso (f.normalizationPullback g))
