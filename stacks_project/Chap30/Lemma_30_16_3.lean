/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 30.16.3

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally projective, and let `ℱ` be a
coherent module on `X`. Then every higher direct image `R^i f_* ℱ` is coherent.
-/
@[stacks 02O4] #check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_isCoherent_of_locallyProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyProjective f]
      (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℕ),
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i).IsCoherent)
