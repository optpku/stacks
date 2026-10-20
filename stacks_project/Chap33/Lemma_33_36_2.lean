/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {p : ℕ} [Fact p.Prime]
  [∀ U : X.Opens, CharP (Γ(X, U)) p] [∀ U : Y.Opens, CharP (Γ(Y, U)) p]
  (f : X ⟶ Y)

/- Lemma 33.36.2: Absolute Frobenius commutes with every morphism of schemes in
characteristic `p`. -/
@[stacks 0CC7]
#check (AlgebraicGeometry.absoluteFrobenius_commSq f :
  CommSq (Scheme.absoluteFrobenius p X) f f (Scheme.absoluteFrobenius p Y))
