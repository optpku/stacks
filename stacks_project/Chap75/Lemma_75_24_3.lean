/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffine.Perfect.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 75.24.3: in Situation 75.24.1, the category of perfect objects of
D(𝒪_X) is the filtered colimit of the categories of perfect objects of
D(𝒪_{X_i}). -/
@[stacks 09RJ] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.isPerfectCategoryColimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
      [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsAffineLimit D),
      s.IsPerfectCategoryColimit)
