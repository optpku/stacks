/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Comparison

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- Small-to-big inverse image of an étale sheaf satisfies ph descent. -/
theorem inverseImage_isSheaf_ph (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (Scheme.bigPhSite S)
      (((siteMorphismOfTopoi S)⁻¹).obj F).1 := sorry

/-- The ph comparison adjunction unit is invertible at the small-to-big
inverse image of an étale sheaf. -/
instance toPhInverseImageUnit_isIso (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    IsIso ((PhComparison.standardComparison .etale S).adjunction.unit.app
      (((siteMorphismOfTopoi S)⁻¹).obj F)) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig
