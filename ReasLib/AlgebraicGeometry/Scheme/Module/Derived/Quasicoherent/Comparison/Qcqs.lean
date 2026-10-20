/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension

/-!
# Comparison for qcqs schemes

This module gives a local-to-global criterion for the comparison between the derived category
of quasicoherent modules and the ambient derived category with quasicoherent cohomology.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On a qcqs scheme, if derived pushforward from every affine open commutes with the canonical
comparisons, then the comparison and the restricted derived coherator are quasi-inverse. -/
theorem comparison_isQuasiInverse {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (h_affinePushforward : ∀ U : X.affineOpens,
      IsIsomorphic (QCoh.Derived.pushforward U.1.ι ⋙ comparison X)
        (comparison (U : Scheme.{u}) ⋙ pushforwardCohomologyIn U.1.ι)) :
    (comparison X).IsQuasiInverse
      ((DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
        (Scheme.Modules.ringedSpaceEquivalence X).mapDerivedCategory.inverse ⋙
        QCoh.Derived.coherator X) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
