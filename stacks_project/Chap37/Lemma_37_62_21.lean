module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul.Locus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.21 (1): if `X` and `Y` are flat and locally of finite presentation over
`S`, then the locus where an `S`-morphism `f : X ⟶ Y` is Koszul is open in `X`. -/
@[stacks 06B8]
#check
  (AlgebraicGeometry.Scheme.Hom.isOpen_koszulAt_locus :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (pX : X ⟶ S) (pY : Y ⟶ S)
      (h_over : f ≫ pY = pX) [AlgebraicGeometry.Flat pX]
      [AlgebraicGeometry.LocallyOfFinitePresentation pX] [AlgebraicGeometry.Flat pY]
      [AlgebraicGeometry.LocallyOfFinitePresentation pY],
      IsOpen {x : X | f.KoszulAt x})

/- Lemma 37.62.21 (2): under an arbitrary base change `g : S' ⟶ S`, the locus where
`f` is Koszul pulls back to the locus where the base-changed morphism `f'` is Koszul. -/
@[stacks 06B8]
#check
  (AlgebraicGeometry.Scheme.Hom.koszulAt_locus_eq_preimage_of_baseChange :
    ∀ {X' X Y' Y S' S : AlgebraicGeometry.Scheme.{u}}
      (f' : X' ⟶ Y') (f : X ⟶ Y) (pX' : X' ⟶ S') (pX : X ⟶ S)
      (pY' : Y' ⟶ S') (pY : Y ⟶ S) (gX : X' ⟶ X) (gY : Y' ⟶ Y)
      (g : S' ⟶ S) (h_over' : f' ≫ pY' = pX') (h_over : f ≫ pY = pX)
      (sq : CommSq f' gX gY f) (hX : IsPullback gX pX' pX g)
      (hY : IsPullback gY pY' pY g) [AlgebraicGeometry.Flat pX]
      [AlgebraicGeometry.LocallyOfFinitePresentation pX] [AlgebraicGeometry.Flat pY]
      [AlgebraicGeometry.LocallyOfFinitePresentation pY],
      {x' : X' | f'.KoszulAt x'} = gX ⁻¹' {x : X | f.KoszulAt x})
