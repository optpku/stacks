module

public import stacks_project.Chap75.Lemma_75_24_3_Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit

universe u

/- Lemma 75.24.3: in Situation 75.24.1, the category of perfect objects of
D(𝒪_X) is the filtered colimit of the categories of perfect objects of
D(𝒪_{X_i}). -/
@[stacks 09RJ] #check
  (isPerfectCategoryColimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
      [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsAffineLimit D),
      s.IsPerfectCategoryColimit)
