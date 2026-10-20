/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Chow.Embedding
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.40.2: A finite-type separated morphism with a specified immersion
of a quasi-compact open into relative projective space admits a compatible
admissible-blowup embedding into a proper representable algebraic space. -/
@[stacks 088R] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_closedImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [FiniteType f] [Separated f]
    (U : OpenSubspace X) [IsQuasiCompact U.X]
    (n : ℕ) (i : U.X ⟶ ProjectiveSpace n Y) [IsImmersion i]
    (h_over : i ≫ ProjectiveSpace.toBase n Y = U.ι ≫ f),
    ∃ (X' Z' Z : AlgebraicSpace S)
      (bX : X' ⟶ X) (j : X' ⟶ Z') (bZ : Z' ⟶ Z)
      (c : Z ⟶ ProjectiveSpace n Y)
      (ιX' : U.X ⟶ X') (ιZ' : U.X ⟶ Z') (ιZ : U.X ⟶ Z)
      (hιX' : IsOpenImmersion ιX') (hιZ' : IsOpenImmersion ιZ')
      (hιZ : IsOpenImmersion ιZ),
      IsAdmissibleBlowup U bX ∧ IsOpenImmersion j ∧
        Proper (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        yoneda.relativelyRepresentable (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        IsAdmissibleBlowup ⟨U.X, ιZ, hιZ⟩ bZ ∧
        IsClosedImmersion c ∧
        ιX' ≫ bX = U.ι ∧ ιX' ≫ j = ιZ' ∧ ιZ' ≫ bZ = ιZ ∧
        ιZ ≫ c = i ∧
        bX ≫ f = j ≫ bZ ≫ c ≫ ProjectiveSpace.toBase n Y)
