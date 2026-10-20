/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative

/-!
# Quasi-affine morphisms and relatively ample structure sheaves

A morphism of algebraic spaces is quasi-affine exactly when its structure sheaf
is relatively ample.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is quasi-affine if and only if its structure
sheaf is relatively ample. -/
theorem quasiAffine_iff_structureSheaf_relativelyAmple
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    QuasiAffine f ↔
      RelativelyAmple f (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

/-- A quasi-affine morphism of algebraic spaces has relatively ample structure
sheaf. -/
instance RelativelyAmple.of_quasiAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [hf : QuasiAffine f] :
    RelativelyAmple f (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  (quasiAffine_iff_structureSheaf_relativelyAmple f).mp hf

/-- Relative ampleness of the structure sheaf witnesses that a morphism of
algebraic spaces is quasi-affine. -/
instance QuasiAffine.of_relativelyAmple_structureSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [hf : RelativelyAmple f (SheafOfModules.unit (structureSheaf X) : X.Modules)] :
    QuasiAffine f :=
  (quasiAffine_iff_structureSheaf_relativelyAmple f).mpr hf

end AlgebraicGeometry.AlgebraicSpace
