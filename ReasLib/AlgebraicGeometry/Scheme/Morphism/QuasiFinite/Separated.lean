/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally quasi-finite morphism with locally Artinian target is separated. -/
instance isSeparated_of_locallyQuasiFinite_of_isLocallyArtinian
    {X S : Scheme} (f : X ⟶ S) [LocallyQuasiFinite f] [IsLocallyArtinian S] :
    IsSeparated f := by
  have : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  have : IsLocallyArtinian (pullback f f) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.fst f f)
  exact ⟨IsClosedImmersion.of_isPreimmersion (pullback.diagonal f)
    (isClosed_discrete _)⟩

end AlgebraicGeometry
