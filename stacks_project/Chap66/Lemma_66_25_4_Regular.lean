/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular

@[expose] public section

universe u

/-! Compatibility checks for the regular algebraic-space API. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsRegular :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    AlgebraicGeometry.AlgebraicSpace S → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.IsRegular.spec :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsRegular X],
    AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale
      (AlgebraicGeometry.Scheme.Regular :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u}) X)
#check (AlgebraicGeometry.AlgebraicSpace.IsRegular.of :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X : AlgebraicGeometry.AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale
      (AlgebraicGeometry.Scheme.Regular :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u}) X →
      AlgebraicGeometry.AlgebraicSpace.IsRegular X)
#check (AlgebraicGeometry.AlgebraicSpace.IsRegular.instIsNormal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsRegular X],
    AlgebraicGeometry.AlgebraicSpace.IsNormal X)
#check (AlgebraicGeometry.AlgebraicSpace.instIsRegular_ofOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (T : CategoryTheory.Over S)
    [AlgebraicGeometry.Scheme.Regular T.left],
    AlgebraicGeometry.AlgebraicSpace.IsRegular
      (AlgebraicGeometry.AlgebraicSpace.ofOver T))
#check (AlgebraicGeometry.AlgebraicSpace.isRegular_iff_forallEtale :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsRegular X ↔
      AlgebraicGeometry.AlgebraicSpace.forallEtale
        (AlgebraicGeometry.Scheme.Regular :
          CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u}) X)
