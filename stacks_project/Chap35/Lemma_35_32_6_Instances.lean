/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion

@[expose] public section

open CategoryTheory

universe u

/- The reusable criterion remains available through this compatibility module. -/
#check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.of_isLocalAtSource_isLocalAtTarget :
    ∀ (P : MorphismProperty AlgebraicGeometry.Scheme.{u})
      [P.IsLocalAtSource AlgebraicGeometry.Scheme.etalePrecoverage]
      [P.IsLocalAtTarget AlgebraicGeometry.Scheme.etalePrecoverage]
      [P.RespectsRight
        (@AlgebraicGeometry.IsOpenImmersion :
          MorphismProperty AlgebraicGeometry.Scheme.{u})],
      AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P)
