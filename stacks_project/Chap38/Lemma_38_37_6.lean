module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Flattening
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 38.37.6: a finitely presented morphism that is flat over a quasi-compact open
admits compatible almost blowup squares whose transformed morphism is flat and finitely
presented, with center disjoint from the open. Here `Z = I.subscheme`,
`E = (I.comap b).subscheme`, `T = (I.comap f).subscheme`, and `D` is the pullback of `T`
along `strictTransformFst b (I.comap b) f`; these comap descriptions give the lower and top
cartesian squares. -/
@[stacks 0EVC] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isAlmostBlowupSquare_flattening :
    ∀
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f]
    (V : Y.Opens) [QuasiCompact V.ι] [Flat (f ∣_ V)],
    ∃ (Y' : Scheme.{u}) (b : Y' ⟶ Y) (I : Y.IdealSheafData),
      IsAlmostBlowupSquare b I ∧
        IsAlmostBlowupSquare (strictTransformFst b (I.comap b) f) (I.comap f) ∧
        Disjoint (I.support : Set Y) V ∧
        Flat (strictTransformSnd b (I.comap b) f) ∧
        Scheme.Hom.FinitePresentation (strictTransformSnd b (I.comap b) f))

end AlgebraicGeometry.Scheme.Hom
