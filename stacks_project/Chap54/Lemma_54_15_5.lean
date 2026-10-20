/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.IdealPrincipalization
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.15.5 (local erratum): on a Noetherian regular scheme `X` of dimension `2`,
a closed subscheme `Z` with nowhere dense support becomes an effective Cartier divisor
after finitely many closed-point blowups. Noetherianity and nowhere dense support are
explicit corrections needed by the cited Tag 0AGB; the uploaded source is unchanged. -/
@[stacks 0BIB] #check (AlgebraicGeometry.Scheme.existsEffectiveCartierInverseImageAfterPointBlowups :
  ∀ (X : Scheme.{u}) [IsNoetherian X] [Regular X],
    topologicalKrullDim X = 2 →
    ∀ (Z : X.IdealSheafData), interior (closure Z.supportSet) = ∅ →
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      IsEffectiveCartierDivisor (Z.comap s.toSource).subschemeι)

end AlgebraicGeometry.Scheme
