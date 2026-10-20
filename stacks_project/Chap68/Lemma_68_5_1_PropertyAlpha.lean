/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyAlpha

/-!
# Property (α) for algebraic spaces

An algebraic space has property (α) when every point satisfies the affine étale
finite-fibre test of Lemma 68.4.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.HasPropertyAlpha :
  {S : Scheme.{u}} → AlgebraicSpace S → Prop)
