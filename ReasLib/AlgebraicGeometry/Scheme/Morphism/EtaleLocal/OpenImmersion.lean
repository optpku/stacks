/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget

/-- Étale locality on the source and target, together with stability under
postcomposition by open immersions, implies étale locality on source-and-target. -/
@[instance 100]
theorem of_isLocalAtSource_isLocalAtTarget
    (P : MorphismProperty Scheme.{u}) [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})] :
    IsEtaleLocalAtSourceAndTarget P := sorry

end AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
