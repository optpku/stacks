/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible

/-!
# Relatively ample invertible modules after admissible blowups

An admissible blowup of a closed subspace of projective space over a
quasi-compact algebraic space admits an invertible relatively ample module.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativelyAmple

/-- An admissible blowup of a closed subspace of projective space over a
quasi-compact algebraic space admits an invertible module relatively ample
for the composite morphism to the base. -/
theorem exists_of_admissibleBlowup_closedImmersion
    {S : Scheme.{u}} {Y Z' Z : AlgebraicSpace S} [IsQuasiCompact Y]
    (n : ℕ) (U : OpenSubspace Z) (bZ : Z' ⟶ Z)
    (c : Z ⟶ ProjectiveSpace n Y) (hbZ : IsAdmissibleBlowup U bZ)
    [IsClosedImmersion c] :
    ∃ L : Z'.Modules, isInvertibleObject L ∧
      RelativelyAmple (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativelyAmple
