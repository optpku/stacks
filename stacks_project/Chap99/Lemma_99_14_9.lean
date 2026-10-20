module

public import ReasLib.AlgebraicGeometry.Polarized.Pushout
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.Functor

universe u

/- Lemma 99.14.9. Restriction of polarized families across a pushout square of
schemes is an equivalence when the top horizontal morphism is a thickening and
the left vertical morphism is affine. -/
@[stacks 0D44] #check (AlgebraicGeometry.Polarized.toPullback_isEquivalence :
  ∀ {T T' S S' : Scheme.{u}} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    [IsThickening i] [IsAffineHom f] (H : IsPushout i f g h),
    (AlgebraicGeometry.Polarized.toPullback i f g h H).IsEquivalence)
