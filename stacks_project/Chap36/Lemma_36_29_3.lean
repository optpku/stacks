/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.Perfect.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 36.29.3: in a directed inverse system of quasi-compact,
quasi-separated schemes with affine transition maps, the perfect derived category
of the specified limit is the filtered colimit of the perfect derived categories
at finite stages. -/
@[stacks 09RF] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.isPerfectCategoryColimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ Scheme.{u}}
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
      (s : Scheme.Limit.QcqsAffineLimit D),
      s.IsPerfectCategoryColimit)
