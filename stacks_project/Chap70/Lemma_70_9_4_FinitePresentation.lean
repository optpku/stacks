/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.FinitePresentation
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Filtered colimits of finitely presented algebras on QCQS algebraic spaces

If `X` is a quasi-compact quasi-separated algebraic space over a scheme `S`,
every quasi-coherent `𝒪_X`-algebra is a small filtered colimit of finitely
presented quasi-coherent `𝒪_X`-algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Quasi-coherent algebras on a QCQS algebraic space are filtered colimits of finitely
presented quasi-coherent algebras. -/
#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finitelyPresentable_ind :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder),
    (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finitelyPresentableProperty X).ind.{u} A.obj)

