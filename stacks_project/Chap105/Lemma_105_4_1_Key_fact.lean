/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.FiberProduct
import StacksCheckRecall

/-!
# Fibre products of morphisms into the moduli stack of elliptic curves
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 105.4.1 (Key fact): The presheaf of triples of base morphisms and
section-preserving cartesian isomorphisms between the corresponding pullbacks is
representable by a scheme. -/
@[stacks 072M] #check
  (AlgebraicGeometry.EllipticCurve.functor_isRepresentable :
    ∀ {S S' : Scheme.{u}} (E : Over S) (zero : S ⟶ E.left)
      (E' : Over S') (zero' : S' ⟶ E'.left)
      [AlgebraicGeometry.EllipticCurve.IsEllipticCurve E zero]
      [AlgebraicGeometry.EllipticCurve.IsEllipticCurve E' zero'],
      (AlgebraicGeometry.EllipticCurve.functor E zero E' zero').IsRepresentable)
