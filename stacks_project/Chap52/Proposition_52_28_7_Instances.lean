/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Noetherian

open AlgebraicGeometry

noncomputable section

@[expose] public section

universe u

/- Compatibility check for the canonical proper-scheme Noetherian instance. -/
#check
  (AlgebraicGeometry.SchemeOverField.instIsNoetherianOfProper :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom],
      IsNoetherian P.left)
