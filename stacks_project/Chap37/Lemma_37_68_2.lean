/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.FiniteLocallyFree

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/- Lemma 37.68.2 -/
@[stacks 0BL3] #check (AlgebraicGeometry.Scheme.RelativeHom.representableByAffineOfFiniteLocallyFree :
  ∀ {S : Scheme.{u}} (Z X : Over S) [IsFiniteLocallyFree Z.hom] [IsAffineHom X.hom],
    ∃ (H : Over S) (hH : IsAffineHom H.hom),
      Nonempty ((functor Z X).RepresentableBy H))

end AlgebraicGeometry.Scheme.RelativeHom
