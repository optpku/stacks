/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Lift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform

/-!
# Scheme-theoretic images under admissible blowups

The scheme-theoretic image of a quasi-compact morphism supported over an open
subspace becomes its strict transform after an admissible blowup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The projection to the first factor of the scheme-theoretic image of a
quasi-compact morphism into a fibre product. -/
def imageFst {S : Scheme.{u}} {B X Y V : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q] :
    (Hom.schemeTheoreticImage q).X ⟶ X :=
  (Hom.schemeTheoreticImage q).ι ≫ pullback.fst f g

/-- The image projection is the kernel-subscheme inclusion followed by the
first fibre-product projection. -/
theorem imageFst_eq {S : Scheme.{u}} {B X Y V : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q] :
    imageFst f g q = (Hom.schemeTheoreticImage q).ι ≫ pullback.fst f g :=
  rfl

/-- The exceptional complement in the base change of a scheme-theoretic image
along a blowup is a quasi-compact open subspace. -/
theorem quasiCompact_strictTransformOpenComplement_imageFst
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    QuasiCompact
      (strictTransformOpenComplement b (center.inverseImageSubspace b) (imageFst f g q)).ι :=
  sorry

/-- The strict transform of the scheme-theoretic image in its base change
along a blowup, relative to the exceptional inverse image of the center. -/
def strictTransformImage {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    ClosedSubspace (strictTransformAmbient b (imageFst f g q)) :=
  @strictTransform S X X' _ b (center.inverseImageSubspace b) (imageFst f g q)
    (quasiCompact_strictTransformOpenComplement_imageFst f g q b center hb)

/-- The ideal sheaf of the strict transform of an image consists of
structure-sheaf sections supported on the pulled-back exceptional divisor. -/
theorem strictTransformImage_idealSheaf
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    (strictTransformImage f g q b center hb).idealSheaf =
      strictTransformIdeal b (center.inverseImageSubspace b) (imageFst f g q) :=
  @strictTransform_idealSheaf S X X' _ b (center.inverseImageSubspace b) (imageFst f g q)
    (quasiCompact_strictTransformOpenComplement_imageFst f g q b center hb)

/-- The projections of the strict transform of an image commute over the
base of the original fibre product. -/
theorem strictTransformImageMap_condition
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    ((strictTransformImage f g q b center hb).ι ≫ pullback.snd (imageFst f g q) b) ≫
        (b ≫ f) =
      ((strictTransformImage f g q b center hb).ι ≫ pullback.fst (imageFst f g q) b ≫
        (Hom.schemeTheoreticImage q).ι ≫ pullback.snd f g) ≫ g :=
  sorry

/-- The canonical embedding of the strict transform of a scheme-theoretic
image into the blown-up fibre product. -/
def strictTransformImageMap {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    (strictTransformImage f g q b center hb).X ⟶ pullback (b ≫ f) g :=
  pullback.lift
    ((strictTransformImage f g q b center hb).ι ≫ pullback.snd (imageFst f g q) b)
    ((strictTransformImage f g q b center hb).ι ≫ pullback.fst (imageFst f g q) b ≫
      (Hom.schemeTheoreticImage q).ι ≫ pullback.snd f g)
    (strictTransformImageMap_condition f g q b center hb)

/-- The first projection of the strict-transform embedding is its projection
to the blown-up space. -/
theorem strictTransformImageMap_fst
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    strictTransformImageMap f g q b center hb ≫ pullback.fst (b ≫ f) g =
      (strictTransformImage f g q b center hb).ι ≫ pullback.snd (imageFst f g q) b :=
  sorry

/-- The second projection of the strict-transform embedding is induced by
the projection of the original scheme-theoretic image. -/
theorem strictTransformImageMap_snd
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    strictTransformImageMap f g q b center hb ≫ pullback.snd (b ≫ f) g =
      (strictTransformImage f g q b center hb).ι ≫ pullback.fst (imageFst f g q) b ≫
        (Hom.schemeTheoreticImage q).ι ≫ pullback.snd f g :=
  sorry

/-- The canonical strict-transform embedding into the blown-up fibre product
is a closed immersion. -/
theorem isClosedImmersion_strictTransformImageMap
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) (hb : IsBlowup b center) :
    IsClosedImmersion (strictTransformImageMap f g q b center hb) :=
  sorry

/-- Lifting a quasi-compact morphism whose first projection factors through
an open subspace along an admissible blowup replaces its scheme-theoretic
image by the strict transform, as equality of ideal subobjects in the
blown-up fibre product. -/
theorem image_liftAdmissible_isomorphic_strictTransform
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X) (center : ClosedSubspace X)
    (hb : IsAdmissibleBlowupCenter U b center)
    (qU : V ⟶ U.X) (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    Hom.idealSheafSubobject (liftAdmissiblePullback f g q U b qU
        (isIso_pullbackFst_of_isAdmissibleBlowupCenter U b center hb) hqU) =
      Hom.idealSheafSubobject (strictTransformImageMap f g q b center hb.isBlowup) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
