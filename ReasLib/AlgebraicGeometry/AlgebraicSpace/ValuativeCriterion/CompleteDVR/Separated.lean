/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.CompleteDVR
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Separated

/-!
# Noetherian complete DVR criterion for separated morphisms of algebraic spaces
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- If
`f : X ⟶ Y` is a morphism of algebraic spaces over a scheme `S`, `Y` is locally
Noetherian, `f` is locally of finite type and quasi-separated, and every
complete DVR valuative square has at most one lift, then `f` is separated. -/
instance of_completeDvrUniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.CompleteDVR.Uniqueness f] : Separated f :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace
