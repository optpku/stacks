/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.Polynomial
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- 92.25.0.1: objects of C_{X/Λ} are commutative squares of schemes
X ← U over Spec(Λ) ← A, where U is an open subscheme of the Λ-scheme X
and A is a vertex isomorphic over Spec(Λ) to a polynomial affine space. -/
@[stacks 08V8]
#check (AlgebraicGeometry.Scheme.Over.Polynomial.Object :
  (R : CommRingCat.{u}) → (X : Scheme.{u}) → [X.Over (Spec R)] → Type (u + 1))
