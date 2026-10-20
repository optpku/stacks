/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.LocalCompleteIntersection

/-!
# Local complete intersection morphisms from regular immersions

Koszul-regular immersions of algebraic spaces over a scheme are local complete
intersection morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsKoszulRegularImmersion

/-- A Koszul-regular immersion of algebraic spaces over a scheme is a local
complete intersection morphism. -/
@[instance]
theorem isLocalCompleteIntersection {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (i : X ⟶ Y) [IsKoszulRegularImmersion i] :
    IsLocalCompleteIntersection i :=
  sorry

end IsKoszulRegularImmersion

end AlgebraicGeometry.AlgebraicSpace
