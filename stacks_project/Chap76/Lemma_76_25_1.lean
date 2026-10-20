/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.IntegralClosure.Pullback
import StacksCheckRecall

/-!
# Smooth pullback of integral closures of quasi-coherent algebras

Formation of the integral closure of the structure sheaf in a quasi-coherent algebra
commutes with smooth pullback, compatibly with inclusion into the pulled-back algebra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

/- Lemma 76.25.1. For a smooth morphism of algebraic spaces over a scheme, integral closure
of the structure sheaf in a quasi-coherent algebra commutes with pullback. -/
@[stacks 082E] #check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.toIntegralClosure_isIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [AlgebraicGeometry.AlgebraicSpace.Smooth f] (A : X.QcAlgebraUnder),
    CategoryTheory.IsIso (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.toIntegralClosure f A))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.toIntegralClosure_comp_inclusion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) (A : X.QcAlgebraUnder),
    toIntegralClosure f A ≫ inclusion ((pullback f).obj A) =
      (pullback f).map (inclusion A))
