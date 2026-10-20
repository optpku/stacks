/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Chow

/-!
# Chow's lemma for algebraic spaces

A separated finite-type morphism of algebraic spaces into a separated Noetherian
algebraic space admits a dense open on the source that, after a `U`-admissible
blowup, immerses into a relative projective space.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.40.5 (Chow's lemma): Let `S` be a scheme. Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S`. Assume `f` is separated of finite type,
and `Y` is separated and Noetherian. Then there exists a commutative diagram
in which `X' ⟶ X` is a `U`-admissible blowup for some dense open `U ⊂ X` and
the morphism `X' ⟶ ProjectiveSpace n Y` is an immersion. -/
@[stacks 088U]
#check (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isAdmissibleBlowup_isImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Separated f]
    [IsAbsolutelySeparated Y] [IsNoetherian Y],
    ∃ (U : OpenSubspace X) (n : ℕ) (X' : AlgebraicSpace S)
      (bX : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n Y),
      Dense (U.pointsSet : Set (Points X)) ∧
        IsAdmissibleBlowup U bX ∧ IsImmersion i ∧
        bX ≫ f = i ≫ ProjectiveSpace.toBase n Y)

end AlgebraicGeometry.AlgebraicSpace
