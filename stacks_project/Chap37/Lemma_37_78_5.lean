module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.CompletelyDecomposed
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/- Lemma 37.78.5: if a locally finitely presented morphism over one stage of a
directed inverse system with affine transition morphisms becomes completely
decomposed over the limit, then it is completely decomposed over some later
stage, provided its target is quasi-compact and quasi-separated. -/
@[stacks 0GTM]
#check (AlgebraicGeometry.Scheme.Limit.exists_completelyDecomposed_stage :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i0 : I)
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (X0 Y0 : Over (D.obj i0)) (f0 : X0 ⟶ Y0)
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [LocallyOfFinitePresentation f0.left]
    [Scheme.Hom.CompletelyDecomposed ((Over.pullback (c.π.app i0)).map f0).left],
    ∃ (i : I) (hi0i : i0 ≤ i),
      Scheme.Hom.CompletelyDecomposed
        ((Over.pullback (D.map (homOfLE hi0i))).map f0).left)

end AlgebraicGeometry.Scheme.Limit
