/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.FiniteProductColimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

/- Lemma 39.7.12: if `A` is a directed colimit of finite products of copies of a field `k`,
then for every `k`-scheme `X` the canonical map from `|Spec(A) ×ₖ X|` to
`|Spec(A)| × |X|` is a homeomorphism. -/
@[stacks 0B7T]
#check
  (AlgebraicGeometry.Scheme.Pullback.toProduct_isHomeomorph_of_finitePiColimit :
    ∀ {k I : Type u} [Field k] [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (F : I ⥤ CommAlgCat.{u} k) (c : Cocone F) (hc : IsColimit c)
      (ι : I → Type u) [∀ i, Finite (ι i)]
      (e : ∀ i, F.obj i ≅ CommAlgCat.of k (ι i → k))
      (X : AlgebraicGeometry.SchemeOverField k),
      let T := AlgebraicGeometry.Scheme.OverSpec.affine
        (CommRingCat.ofHom (algebraMap k c.pt))
      IsHomeomorph (AlgebraicGeometry.Scheme.Pullback.toProduct T X))
