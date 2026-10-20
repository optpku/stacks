module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Henselization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/- Lemma 37.19.4 (Normalization and henselization) (1): pulling the normalization of a
locally Noetherian scheme back to the spectrum of a henselization of a local ring at a point
is the normalization of that spectrum. -/
@[stacks 0CBM]
#check (AlgebraicGeometry.Scheme.Normalization.henselizationBaseChange :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    (Rh : Type u) [CommRing Rh] [Algebra (X.presheaf.stalk x) Rh]
    [IsHenselizationOf (X.presheaf.stalk x) Rh],
    -- Local instance justification (search instability): Rh does not determine its base ring.
    letI : IsNoetherianRing Rh :=
      @IsHenselizationOf.isNoetherianRing (X.presheaf.stalk x) _ _ Rh _ _ _ _
    let g : Spec (CommRingCat.of Rh) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rh)) ≫
        X.fromSpecStalk x
    ∃ e : pullback X.normalizationTo g ≅ (Spec (CommRingCat.of Rh)).normalization,
      pullback.snd X.normalizationTo g =
        e.hom ≫ (Spec (CommRingCat.of Rh)).normalizationTo)

/- Lemma 37.19.4 (Normalization and henselization) (2): pulling the normalization of a
locally Noetherian scheme back to the spectrum of a strict henselization of a local ring at a
point is the normalization of that spectrum. -/
@[stacks 0CBM]
#check (AlgebraicGeometry.Scheme.Normalization.strictHenselizationBaseChange :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    (Rsh : Type u) [CommRing Rsh] [Algebra (X.presheaf.stalk x) Rsh]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Rsh],
    -- Local instance justification (search instability): Rsh does not determine its base ring.
    letI : IsNoetherianRing Rsh :=
      @IsStrictHenselizationOf.isNoetherianRing (X.presheaf.stalk x) _ _ Rsh _ _ _ _
    let g : Spec (CommRingCat.of Rsh) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rsh)) ≫
        X.fromSpecStalk x
    ∃ e : pullback X.normalizationTo g ≅ (Spec (CommRingCat.of Rsh)).normalization,
      pullback.snd X.normalizationTo g =
        e.hom ≫ (Spec (CommRingCat.of Rsh)).normalizationTo)

end AlgebraicGeometry.Scheme.Normalization
