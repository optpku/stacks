/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap78.Definition_78_5_1_Group
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 78.5.1 (1): a group algebraic space over an algebraic space `B` is an
internal group object in the category of algebraic spaces over `B`. -/
@[stacks 043H] #check (AlgebraicGeometry.GroupAlgebraicSpace :
  ∀ {S : Scheme.{u}} (B : AlgebraicGeometry.AlgebraicSpace S), Type (u + 1))

/- Definition 78.5.1 (2): a morphism of group algebraic spaces over `B` is a morphism
of algebraic spaces over `B` inducing a group homomorphism on scheme-valued points. -/
@[stacks 043H] #check (AlgebraicGeometry.GroupAlgebraicSpace.hom_iff_schemePoints :
  ∀ {S : Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    {G G' : AlgebraicGeometry.GroupAlgebraicSpace B} (ψ : G.X ⟶ G'.X),
    IsMonHom ψ ↔
      ∀ (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B),
        ∀ a b : Over.mk t ⟶ G.X, (a ≫ ψ) * (b ≫ ψ) = (a * b) ≫ ψ)
