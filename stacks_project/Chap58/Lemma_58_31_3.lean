/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.RegularCartierExtension
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Lemma 58.31.3: a finite étale cover of the complement of a regular effective Cartier divisor
on a locally Noetherian scheme, unramified over the scheme in codimension one, extends to a
finite étale cover of the whole scheme. -/
@[stacks 0EYE]
#check
  (AlgebraicGeometry.Scheme.FiniteEtale.exists_extension_of_unramifiedInCodimensionOne_of_regularCartier :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : Scheme.FiniteEtale (closedImmersionComplement i).toScheme)
      (hY : IsUnramifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y),
      ∃ Y' : Scheme.FiniteEtale X,
        Nonempty ((finiteEtaleBaseChange (closedImmersionComplement i).ι).obj Y' ≅ Y))

end AlgebraicGeometry.Scheme.FiniteEtale
