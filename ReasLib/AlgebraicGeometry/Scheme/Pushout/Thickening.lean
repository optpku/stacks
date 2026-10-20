module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Colimit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.SurjectivePullback
public import ReasLib.RingTheory.Pullback.LocalizationAway

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout

/-- A thickening and an affine morphism with common source have a pushout in the
category of schemes. -/
instance instHasPushoutThickeningAffine {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [IsAffineHom f] : HasPushout i f := sorry

/-- The canonical morphism from the target of an affine morphism to the pushout along
a thickening is a thickening. -/
instance instInrIsThickening {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [IsAffineHom f] :
    IsThickening (pushout.inr i f) := sorry

/-- The canonical pushout square of a thickening and an affine morphism is cartesian. -/
theorem isPullback {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [IsAffineHom f] :
    IsPullback i f (pushout.inl i f) (pushout.inr i f) := sorry

/-- On every open of the canonical pushout of a thickening and an affine morphism,
its section ring is the pullback of the corresponding section rings on the other
three schemes. -/
theorem structureSheaf_isPullback {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [IsAffineHom f] :
    IsStructureSheafPullback (IsPushout.of_hasPushout i f).toCommSq := sorry

end AlgebraicGeometry.Scheme.Pushout
