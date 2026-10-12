/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

/-!
# Normalization and henselization

This module records that normalization of a locally Noetherian scheme commutes with base change
to a henselization or strict henselization of a stalk.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/-- Pulling the normalization of a locally Noetherian scheme back to the spectrum of a
henselization of a stalk gives the normalization of that spectrum. -/
theorem henselizationBaseChange (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    (Rh : Type u) [CommRing Rh] [Algebra (X.presheaf.stalk x) Rh]
    [IsHenselizationOf (X.presheaf.stalk x) Rh] :
    -- Local instance justification (search instability): Rh does not determine its base ring.
    letI : IsNoetherianRing Rh :=
      @IsHenselizationOf.isNoetherianRing (X.presheaf.stalk x) _ _ Rh _ _ _ _
    let g : Spec (CommRingCat.of Rh) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rh)) ≫
        X.fromSpecStalk x
    ∃ e : pullback X.normalizationTo g ≅ (Spec (CommRingCat.of Rh)).normalization,
      pullback.snd X.normalizationTo g =
        e.hom ≫ (Spec (CommRingCat.of Rh)).normalizationTo := sorry

/-- Pulling the normalization of a locally Noetherian scheme back to the spectrum of a strict
henselization of a stalk gives the normalization of that spectrum. -/
theorem strictHenselizationBaseChange (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    (Rsh : Type u) [CommRing Rsh] [Algebra (X.presheaf.stalk x) Rsh]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Rsh] :
    -- Local instance justification (search instability): Rsh does not determine its base ring.
    letI : IsNoetherianRing Rsh :=
      @IsStrictHenselizationOf.isNoetherianRing (X.presheaf.stalk x) _ _ Rsh _ _ _ _
    let g : Spec (CommRingCat.of Rsh) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rsh)) ≫
        X.fromSpecStalk x
    ∃ e : pullback X.normalizationTo g ≅ (Spec (CommRingCat.of Rsh)).normalization,
      pullback.snd X.normalizationTo g =
        e.hom ≫ (Spec (CommRingCat.of Rsh)).normalizationTo := sorry

end AlgebraicGeometry.Scheme.Normalization
