/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_52_9_Colimit
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
      [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
      (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
      [Flat x₀] [FinitePresentation x₀],
      s.IsPerfectOverCategoryColimit x₀)
