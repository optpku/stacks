module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskisMainTheorem
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.34.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is of finite type and separated. Let `Y'` be
the normalization of `Y` in `X`, namely `Hom.normalization f`, with the
canonical factorization `toNormalization f ≫ fromNormalization f = f`. Then
there exists an open subspace `ι : U' ⟶ Hom.normalization f` such that
`openInverseImageTo (toNormalization f) ι` is an isomorphism, and
`Set.range (Points.map (openInverseImageι (toNormalization f) ι))` is the set
of points of `X` at which `f` is quasi-finite. -/
@[stacks 082I] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.FiniteType.exists_isIso_openInverseImageTo_toNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FiniteType f] [Separated f],
      ∃ (U' : AlgebraicSpace S) (ι : U' ⟶ Hom.normalization f)
        (hι : IsOpenImmersion ι),
        IsIso (openInverseImageTo (Hom.toNormalization f) ι) ∧
          Set.range (Points.map (openInverseImageι (Hom.toNormalization f) ι)) =
            {x | QuasiFiniteAt f x})
