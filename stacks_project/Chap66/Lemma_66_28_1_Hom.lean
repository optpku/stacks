/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-! Compatibility facade for actual internal commutative-ring inverse/direct images. -/

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheafMap :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheaf f ⟶
      AlgebraicGeometry.AlgebraicSpace.commStructureSheaf X)
