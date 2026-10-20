/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PointExt

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open scoped AlgebraicGeometry

universe u

/- Exercise 111.48.2
Let `k` be a field and `Z` a closed `k`-rational point of projective `n`-space,
viewed as a closed subscheme; for example, the point `(1 : 0 : … : 0)`.
The dimension of `Ext^i(𝒪_Z, 𝒪_Z)` is binomial in nonnegative degrees and zero
in negative degrees.
-/
@[stacks 0DD2] #check (AlgebraicGeometry.ProjectiveSpace.finrank_extValue :
  ∀ {k : Type u} [Field k] (n : ℕ)
    (z : Spec (CommRingCat.of k) ⟶ AlgebraicGeometry.ProjectiveSpace.scheme k n)
    (hz : z ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k n = 𝟙 _) (i : ℤ),
    Module.finrank k (AlgebraicGeometry.ProjectiveSpace.extValue z hz i) =
      if 0 ≤ i then n.choose i.toNat else 0)
