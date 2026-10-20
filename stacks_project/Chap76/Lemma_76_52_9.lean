/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.BaseChange.RelativePerfect.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 76.52.9: In Situation 76.52.7 the category of `Y`-perfect objects of
`D(𝒪_X)` is the colimit of the categories of `Yᵢ`-perfect objects of `D(𝒪_{Xᵢ})`. -/
@[stacks 0DKW] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.isPerfectOverCategoryColimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}

      [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
      (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
      [Flat x₀] [FinitePresentation x₀],
      s.IsPerfectOverCategoryColimit x₀)
