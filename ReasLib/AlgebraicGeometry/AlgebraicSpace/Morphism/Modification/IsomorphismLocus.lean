/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational.DenseOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IsomorphismLocus

/-!
# Isomorphism loci of modifications of algebraic spaces

A modification of integral algebraic spaces is an isomorphism over a nonempty
open subspace of the target, so its isomorphism locus is nonempty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A modification of integral algebraic spaces restricts to an isomorphism
over a nonempty open subspace of the target. -/
theorem exists_nonempty_open_isIso_of_isModification
    {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsModification f] :
    ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧
      IsIso (restrictTo f U) :=
  sorry

/-- The isomorphism locus of a modification of integral algebraic spaces is
nonempty. -/
theorem isomorphismLocus_nonempty_of_isModification
    {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsModification f] :
    (isomorphismLocus f).Nonempty :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
