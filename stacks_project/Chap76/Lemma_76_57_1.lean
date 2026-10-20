/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Blowup
import StacksCheckRecall

/-!
# Admissible blowups and the resolution property

A quasi-compact quasi-separated algebraic space whose points space has finitely
many irreducible components admits a dense quasi-compact open and a
corresponding admissible blowup with the resolution property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.57.1: Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Assume that `|X|` has finitely many
irreducible components. There exists a dense quasi-compact open `U ⊂ X` and a
`U`-admissible blowing up `X' ⟶ X` such that the algebraic space `X'` has the
resolution property. -/
@[stacks 0GV5]
#check (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_hasResolutionProperty :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X],
    ∃ (U : OpenSubspace X) (X' : AlgebraicSpace S) (π : X' ⟶ X),
      IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
        IsAdmissibleBlowup U π ∧
          SheafOfModules.HasResolutionProperty (structureSheaf X'))

end AlgebraicGeometry.AlgebraicSpace
