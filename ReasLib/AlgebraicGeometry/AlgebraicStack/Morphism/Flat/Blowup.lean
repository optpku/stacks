/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Flattening algebraic stacks by admissible blowups

A morphism already flat and locally of finite presentation over a
quasi-compact open admits a flat finitely presented closed transform after
an admissible blowup of its target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A finite-type quasi-separated morphism from an algebraic stack to a
quasi-compact quasi-separated algebraic space, flat and locally of finite
presentation over a quasi-compact open, admits an admissible blowup and a
closed substack of its base change that agrees with the original stack over
that open and is flat and of finite presentation over the blown-up space. -/
theorem exists_isAdmissibleBlowup_flat_finitePresentation
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ Y.toGroupoids)
    [AlgebraicStack.FiniteType f] [AlgebraicStack.QuasiSeparated f]
    (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
    [AlgebraicStack.Flat (pullbackSnd f V.ι)]
    [AlgebraicStack.LocallyOfFinitePresentation (pullbackSnd f V.ι)] :
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y)
      (P : ObjectProperty (pullback f b).total) (hP : Substack.IsClosed (pullback f b) P),
      AlgebraicSpace.IsAdmissibleBlowup V b ∧
        Substack.restrictsTo P hP (pullbackFst (pullbackSnd f b) (V.inverseImage b).ι) ∧
        AlgebraicStack.Flat (Substack.closedInclusion (pullback f b) P hP ≫ pullbackSnd f b) ∧
          AlgebraicStack.FinitePresentation
            (Substack.closedInclusion (pullback f b) P hP ≫ pullbackSnd f b) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
