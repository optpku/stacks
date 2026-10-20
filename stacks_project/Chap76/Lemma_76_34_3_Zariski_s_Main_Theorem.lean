/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Factorization
import StacksCheckRecall

/-!
# Zariski's Main Theorem for algebraic spaces

A quasi-finite separated morphism of algebraic spaces over a scheme, with
quasi-compact quasi-separated target, factors as a quasi-compact open immersion
followed by a finite morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.34.3 (Zariski's Main Theorem): Let `S` be a scheme. Let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`. Assume `f` is quasi-finite and
separated and assume that `Y` is quasi-compact and quasi-separated. Then there
exists a factorization `X ⟶ T ⟶ Y` where `j : X ⟶ T` is a quasi-compact open
immersion and `π : T ⟶ Y` is finite. -/
@[stacks 082K] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.QuasiFinite.exists_openImmersion_finiteFactorization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
    ∃ (T : AlgebraicSpace S) (j : X ⟶ T) (π : T ⟶ Y),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f)

