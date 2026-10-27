/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.HigherDirectImage

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.9.3 (1): the canonical structure-module pushforward unit is invertible
after every base change. -/
@[stacks 0E1J] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.unitToPushforward_isIso_universally :
  ∀ {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
    IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g)))

/- Lemma 109.9.3 (2): the first higher direct image of the structure sheaf is
finite locally free. -/
@[stacks 0E1J] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOne_isFiniteLocallyFree :
  ∀ {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P),
    SheafOfModules.IsFiniteLocallyFree (higherDirectImageOne (hom P)))

/- Lemma 109.9.3 (3): the canonical first higher direct image comparison is
invertible under arbitrary base change. -/
@[stacks 0E1J] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOne_commutesWithBaseChange :
  ∀ {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
    IsIso (higherDirectImageOneBaseChangeHom (hom P) g))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
