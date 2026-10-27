/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition

/-!
# Zero subspaces of restricted sections

The zero subspace of a section on a closed subspace is viewed in the ambient
algebraic space by composing the two closed immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- The zero subspace of a section of an invertible module restricted to a closed
subspace, viewed as a closed subspace of the ambient algebraic space. -/
def zeroSchemeRestrict {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (L : X.Modules) [isInvertibleObject L]
    (s : ((Modules.pullback Y.ι).obj L).sections) : ClosedSubspace X :=
  ofι (zeroSchemeι ((Modules.pullback Y.ι).obj L) s ≫ Y.ι)
    (h := @IsClosedImmersion.comp S _ _ _ _ _
      (zeroScheme ((Modules.pullback Y.ι).obj L) s).isClosedImmersion
      Y.isClosedImmersion)

/-- The inclusion of the restricted zero subspace is the zero-subspace inclusion
on the closed subspace followed by its inclusion in the ambient space. -/
theorem zeroSchemeRestrict_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (L : X.Modules) [isInvertibleObject L]
    (s : ((Modules.pullback Y.ι).obj L).sections) :
    (zeroSchemeRestrict Y L s).ι =
      zeroSchemeι ((Modules.pullback Y.ι).obj L) s ≫ Y.ι :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
