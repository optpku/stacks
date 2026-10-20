/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible.Composition

/-!
# Composition of successive admissible blowups

Successive blowups of a quasi-compact quasi-separated algebraic space that are
admissible over a quasi-compact open subspace compose to a blowup admissible
over the same open subspace.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.19.2: let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `U ⊂ X` be a quasi-compact open
subspace. Let `b : X' ⟶ X` be a `U`-admissible blowup, and let `b' : X'' ⟶ X'`
be a `U`-admissible blowup, with `U` viewed on `X'` as `U.inverseImage b`. Then
the composition `b' ≫ b` is a `U`-admissible blowup. -/
@[stacks 086C] #check (AlgebraicGeometry.AlgebraicSpace.IsAdmissibleBlowup.comp :
  ∀ {S : Scheme.{u}} {X X' X'' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b)
    (b' : X'' ⟶ X') (hb' : IsAdmissibleBlowup (U.inverseImage b) b'),
    IsAdmissibleBlowup U (b' ≫ b))
