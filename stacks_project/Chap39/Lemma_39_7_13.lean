module

public import ReasLib.AlgebraicGeometry.GroupScheme.AffineOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 39.7.13: if `k` is algebraically closed, `G` is a Jacobson group scheme over `k`
whose closed points are `k`-rational, and `T = Spec(A)` for a directed colimit `A` of finite
products of copies of `k`, then the range of every `k`-morphism `T ⟶ G` lies in an affine open
of `G`. -/
@[stacks 0B7U]
#check (AlgebraicGeometry.GroupScheme.exists_affineOpen_containing_range_of_finitePiColimit :
  ∀ {k I : Type u} [Field k] [IsAlgClosed k] [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (G : SchemeOverField k) [GrpObj G] [JacobsonSpace G.left]
    (h_rational : ∀ x : closedPoints G.left, IsIso (G.hom.residueFieldMap x.1))
    (F : I ⥤ CommAlgCat.{u} k) (c : Cocone F) (hc : IsColimit c)
    (ι : I → Type u) [∀ i, Finite (ι i)]
    (e : ∀ i, F.obj i ≅ CommAlgCat.of k (ι i → k)),
    let T := Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap k c.pt))
    ∀ f : T ⟶ G, ∃ U : G.left.affineOpens,
      Set.range f.left.base ⊆ ((U : G.left.Opens) : Set G.left))
