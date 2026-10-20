/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.Blowup

/-!
# Relatively ample invertible sheaves after Chow factorizations

In the Chow diagrams of Lemmas 76.40.2 and 76.40.3 the morphism `g : Z' ⟶ Y`
factors as a `U`-admissible blowup, a closed immersion into projective space
over `Y`, and the structure morphism of that projective space. This file records
the presumed existence of a `g`-ample invertible sheaf on `Z'`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Remark 76.40.4: In Lemmas 76.40.2 and 76.40.3 the morphism `g : Z' ⟶ Y` is
a composition of projective morphisms, namely a `U`-admissible blowup
`bZ : Z' ⟶ Z`, a closed immersion `c : Z ⟶ ProjectiveSpace n Y`, and
`ProjectiveSpace.toBase n Y`. Presumably, by the analogue for algebraic spaces
of Morphisms Lemma 29.37.8, there exists a `g`-ample invertible sheaf on `Z'`.
If this is ever needed, it will be stated and proved here. -/
@[stacks 088T] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.exists_of_admissibleBlowup_closedImmersion :
    ∀ {S : Scheme.{u}} {Y Z' Z : AlgebraicSpace S} [IsQuasiCompact Y]
    (n : ℕ) (U : OpenSubspace Z) (bZ : Z' ⟶ Z)
    (c : Z ⟶ ProjectiveSpace n Y) (hbZ : IsAdmissibleBlowup U bZ)
    [IsClosedImmersion c],
    ∃ L : Z'.Modules, isInvertibleObject L ∧
      RelativelyAmple (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) L)
