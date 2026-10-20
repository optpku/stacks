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

/- Lemma 30.26.10

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type, and let `ℱ`
be a coherent module on `X` with support proper over `S`. Then every higher direct image
`R^p f_* ℱ` is coherent.
-/
@[stacks 08DS] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.isCoherent_of_properSupport :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsLocallyNoetherian S]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f ℱ] (p : ℕ),
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ p).IsCoherent)
