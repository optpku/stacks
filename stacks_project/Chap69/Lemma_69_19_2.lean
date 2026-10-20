/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Proper

/-!
# Lemma 69.19.2

A finite-type quasi-separated morphism of algebraic spaces into a locally
Noetherian algebraic space is proper as soon as every DVR valuative square has
a unique lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.19.2: A finite-type quasi-separated morphism of algebraic spaces
with locally Noetherian target is proper if every DVR valuative square has a
unique lift. -/
@[stacks 0ARK] #check (AlgebraicGeometry.AlgebraicSpace.Proper.of_dvr :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y]
    [AlgebraicGeometry.AlgebraicSpace.FiniteType f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f]
    [AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR f],
    AlgebraicGeometry.AlgebraicSpace.Proper f)
