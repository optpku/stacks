/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Chow
import StacksCheckRecall

/-!
# Chow's lemma for finite-type algebraic spaces

A separated finite-type morphism of algebraic spaces into a qcqs algebraic
space admits a proper surjective approximation that open-immerses into a
proper representable algebraic space over the same base.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.41.1: Let `S` be a scheme. Let `Y` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `f : X ⟶ Y` be a separated
morphism of finite type. Then there exists a commutative diagram of
algebraic spaces over `S` with morphisms `g : X' ⟶ X`, `j : X' ⟶ Xbar'`,
and `p : Xbar' ⟶ Y` such that `g` is proper surjective, `j` is an open
immersion, `p` is proper and representable, and `g ≫ f = j ≫ p`. -/
@[stacks 089L] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isOpenImmersion_proper_surjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [FiniteType f] [Separated f],
    ∃ (X' Xbar' : AlgebraicSpace S) (g : X' ⟶ X) (j : X' ⟶ Xbar')
      (p : Xbar' ⟶ Y),
      Proper g ∧ Surjective g ∧ IsOpenImmersion j ∧ Proper p ∧
        yoneda.relativelyRepresentable p ∧ g ≫ f = j ≫ p)

end AlgebraicGeometry.AlgebraicSpace
