/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.LocalAtTarget
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Normalization

/-!
# Locally quasi-finite morphisms and ind-quasi-affineness

This file relates separated locally quasi-finite scheme morphisms to
ind-quasi-affineness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/-- A locally finite-type morphism of schemes with locally finite fibres is
ind-quasi-affine when it is separated. -/
theorem indQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsSeparated f] : IndQuasiAffineHom f := sorry

end AlgebraicGeometry.LocallyQuasiFinite
