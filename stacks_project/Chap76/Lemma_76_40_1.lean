/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.CommonExtension
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.40.1: Let `S` be a scheme. Let `Y` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `ι1 : U ⟶ X1` and `ι2 : U ⟶ X2`
be open immersions of algebraic spaces over `Y`, and assume `U`, `X1`, `X2`
are of finite type and separated over `Y`. Then there exists a commutative
diagram of algebraic spaces over `Y` in which `X1' ⟶ X1` and `X2' ⟶ X2` are
`U`-admissible blowups, `X1' ⟶ X` and `X2' ⟶ X` are open immersions, and
`X ⟶ Y` is separated of finite type. -/
@[stacks 088Q] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_isOpenImmersion :
    ∀ {S : Scheme.{u}} {Y U X1 X2 : AlgebraicSpace S},
    [IsQuasiCompact Y] → [IsAbsolutelyQuasiSeparated Y] →
    (f1 : X1 ⟶ Y) → (f2 : X2 ⟶ Y) → (fU : U ⟶ Y) →
    [FiniteType f1] → [FiniteType f2] → [FiniteType fU] →
    [Separated f1] → [Separated f2] → [Separated fU] →
    (ι1 : U ⟶ X1) → (ι2 : U ⟶ X2) →
    [IsOpenImmersion ι1] → [IsOpenImmersion ι2] →
    (hι1 : ι1 ≫ f1 = fU) → (hι2 : ι2 ≫ f2 = fU) →
    ∃ (X1' X2' X : AlgebraicSpace S)
      (b1 : X1' ⟶ X1) (b2 : X2' ⟶ X2)
      (j1 : X1' ⟶ X) (j2 : X2' ⟶ X) (pX : X ⟶ Y)
      (u1' : U ⟶ X1') (u2' : U ⟶ X2') (uX : U ⟶ X),
      IsAdmissibleBlowup (OpenSubspace.ofι ι1) b1 ∧
        IsAdmissibleBlowup (OpenSubspace.ofι ι2) b2 ∧
        IsOpenImmersion j1 ∧ IsOpenImmersion j2 ∧
        FiniteType pX ∧ Separated pX ∧
        u1' ≫ b1 = ι1 ∧ u2' ≫ b2 = ι2 ∧
        u1' ≫ j1 = uX ∧ u2' ≫ j2 = uX ∧
        j1 ≫ pX = b1 ≫ f1 ∧ j2 ≫ pX = b2 ≫ f2 ∧
        uX ≫ pX = fU)
