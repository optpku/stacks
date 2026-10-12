/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.BaseChange.RelativePerfect.Colimit

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 36.35.9: In Situation 36.35.7 the category of `S`-perfect objects of
`D(𝒪_X)` is the colimit of the categories of `Sᵢ`-perfect objects of `D(𝒪_{Xᵢ})`. -/
@[stacks 0DI8] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.isPerfectOverCategoryColimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ Scheme.{u}}
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
      (s : Scheme.Limit.QcqsAffineLimit D) (X₀ : Scheme.{u})
      (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
      [Flat x₀] [Scheme.Hom.FinitePresentation x₀],
      s.IsPerfectOverCategoryColimit x₀)
