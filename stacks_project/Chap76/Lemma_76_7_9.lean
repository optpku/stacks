/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Vanishing
import StacksCheckRecall

/-!
Local source erratum for tag 05Z9: the pinned source prints `Ω_{X/S} = 0` for
an immersion `f : X ⟶ Y` over `S`. Its proof, via tag 01UY and étale localization
(04CU), instead gives `Ω_{X/Y} = 0`. The printed formula fails for the identity
immersion of the affine line over a field. We retain the original source and
explicitly use the differentials of `f`, with no additional hypothesis.

The differentials are the common owner from Definition 76.7.2, also used by
Lemma 76.7.3; no parallel reconstruction or zero-object definition is introduced.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 76.7.9, with the explicit local subscript erratum above: the sheaf of
relative differentials `Ω_{X/Y}` of an immersion `f : X ⟶ Y` is zero. -/
@[stacks 05Z9] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isZero_relativeDifferentials_of_isImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsImmersion f],
      IsZero (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isZero_relativeDifferentials_of_mono :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f],
      IsZero (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f))
