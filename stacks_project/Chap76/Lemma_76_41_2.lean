/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Chow
import StacksCheckRecall

/-!
# Chow's lemma for quasi-compact separated algebraic spaces

A separated finite-type morphism of algebraic spaces into a separated
quasi-compact algebraic space admits a proper surjective approximation that
immerses into a relative projective space.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.41.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is separated of finite type, and `Y` is
separated and quasi-compact. Then there exists a commutative diagram in which
`X' ⟶ X` is proper surjective and the morphism `X' ⟶ ProjectiveSpace n Y`
is an immersion. -/
@[stacks 089M] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_proper_surjective_isImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f] [IsAbsolutelySeparated Y] [IsQuasiCompact Y],
    ∃ (n : ℕ) (X' : AlgebraicSpace S) (g : X' ⟶ X)
      (i : X' ⟶ ProjectiveSpace n Y),
      Proper g ∧ Surjective g ∧ IsImmersion i ∧
        g ≫ f = i ≫ ProjectiveSpace.toBase n Y)

end AlgebraicGeometry.AlgebraicSpace
