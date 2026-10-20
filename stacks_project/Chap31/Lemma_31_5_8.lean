/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.5.8: for a quasicoherent module on a scheme, finite generation of the maximal ideal
of the stalk at a point identifies associated and weakly associated membership. -/
@[stacks 05AR] #check
  (AlgebraicGeometry.Scheme.Modules.mem_associatedPoints_iff_mem_weakAss_of_stalk_maximalIdeal_fg :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X),
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).FG →
        (x ∈ ℱ.associatedPoints ↔ x ∈ ℱ.weakAss))

/- On a locally Noetherian scheme, the associated and weakly associated loci of a quasicoherent
module coincide. -/
#check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints_eq_weakAss_of_isLocallyNoetherian :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      [AlgebraicGeometry.IsLocallyNoetherian X],
      ℱ.associatedPoints = ℱ.weakAss)
