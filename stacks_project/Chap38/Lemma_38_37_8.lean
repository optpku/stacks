module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Lemma 38.37.8 (1): a sheaf on the chosen big h site sends a thickening of
finite presentation contravariantly to a bijection of section types. -/
@[stacks 0EVE] #check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.map_bijective_of_isThickening :
    ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : Schh.carrier)
      (F : Sheaf (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S) (Type w))
      {X X' : Over S} (f : X ⟶ X')
      [AlgebraicGeometry.IsThickening
        ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).map f)]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation
        ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).map f)],
      Function.Bijective (F.obj.map f.op))

/- Lemma 38.37.8 (2): a sheaf on the affine chosen big h site sends a thickening
of finite presentation contravariantly to a bijection of section types. -/
@[stacks 0EVE] #check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.affineMap_bijective_of_isThickening :
    ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : Schh.carrier)
      (F : Sheaf (AlgebraicGeometry.ChosenBigHSite.bigAffineTopology Schh S) (Type w))
      {X X' : AlgebraicGeometry.ChosenBigSite.affineSite Schh S} (f : X ⟶ X')
      [AlgebraicGeometry.IsThickening
        ((AlgebraicGeometry.ChosenBigSite.affineToScheme Schh S).map f)]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation
        ((AlgebraicGeometry.ChosenBigSite.affineToScheme Schh S).map f)],
      Function.Bijective (F.obj.map f.op))
