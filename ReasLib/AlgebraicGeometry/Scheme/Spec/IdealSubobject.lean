module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Exact

/-!
# Ideal subobjects on affine spectra

An ideal `I ⊆ R` determines both the quotient closed immersion `Spec (R ⧸ I) ⟶ Spec R`
and the explicit ideal subobject represented by `Ĩ ⟶ 𝒪`. This file identifies those canonical
owners without hiding either datum behind an existence statement.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Spec

variable {R : CommRingCat.{u}}

/-- The closed immersion of affine spectra induced by the quotient map `R ⟶ R ⧸ I`. -/
@[stacks 01IG "affine quotient closed immersion"]
noncomputable def quotientMap (I : Ideal R) :
    Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

namespace quotientMap

/-- Under the canonical affine stalk identifications, the stalk map of an affine quotient is the
local ring homomorphism induced by the quotient map. -/
@[stacks 01IG "affine quotient stalk as localized quotient map"]
noncomputable def stalkArrowIso (I : Ideal R) (q : PrimeSpectrum (R ⧸ I)) :
    Arrow.mk ((Spec.quotientMap I).stalkMap q) ≅
      Arrow.mk (CommRingCat.ofHom <|
        Localization.localRingHom
          (q.comap (Ideal.Quotient.mk I)).asIdeal q.asIdeal
          (Ideal.Quotient.mk I) rfl) :=
  Scheme.arrowStalkMapSpecIso
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) q

end quotientMap

namespace tildeIdeal

/-- The canonical inclusion `Ĩ ⟶ 𝒪` on `Spec R`, in the scheme-module category where the tilde
sheaf is defined. -/
@[stacks 01IG "tilde ideal inclusion"]
noncomputable def ι (I : Ideal R) :
    tilde (ModuleCat.of R I) ⟶ SheafOfModules.unit (Spec R).ringCatSheaf :=
  tilde.map (ModuleCat.ofHom I.subtype) ≫ (tildeSelf (R := R)).hom

/-- The canonical inclusion `Ĩ ⟶ 𝒪` is a monomorphism in the scheme-module category. -/
@[stacks 01IG "tilde ideal is a subobject", instance]
theorem ι_mono (I : Ideal R) : Mono (ι I) := sorry

/-- The inclusion `Ĩ ⟶ 𝒪`, transported to the underlying ringed-space module category. -/
@[stacks 01IG "tilde ideal inclusion on the underlying ringed space"]
noncomputable def toRingedSpaceι (I : Ideal R) :
    (Scheme.Modules.toRingedSpace (Spec R)).obj (tilde (ModuleCat.of R I)) ⟶
      SheafOfModules.unit (Spec R).toRingedSpace.ringCatSheaf :=
  (Scheme.Modules.toRingedSpace (Spec R)).map (ι I)

/-- The transported inclusion `Ĩ ⟶ 𝒪` is a monomorphism. -/
@[stacks 01IG "underlying tilde ideal is a subobject", instance]
theorem toRingedSpaceι_mono (I : Ideal R) : Mono (toRingedSpaceι I) := sorry

/-- The ideal subobject of `Spec R` represented explicitly by `Ĩ ⟶ 𝒪`. -/
@[stacks 01IG "affine tilde ideal subobject"]
noncomputable def subobject (I : Ideal R) : Scheme.IdealSubobject (Spec R) :=
  Subobject.mk (toRingedSpaceι I)

/-- The module represented by the affine ideal subobject is concretely the tilde sheaf `Ĩ`. -/
@[stacks 01IG "affine ideal subobject is tilde"]
noncomputable def moduleIso (I : Ideal R) :
    (subobject I).toModule ≅
      (Scheme.Modules.toRingedSpace (Spec R)).obj (tilde (ModuleCat.of R I)) :=
  Subobject.underlyingIso (toRingedSpaceι I)

/-- The concrete tilde comparison identifies the represented subobject arrow with `Ĩ ⟶ 𝒪`. -/
@[reassoc (attr := simp), stacks 01IG "tilde ideal arrow comparison"]
theorem moduleIso_hom_arrow (I : Ideal R) :
    (moduleIso I).hom ≫ toRingedSpaceι I = (subobject I).arrow := sorry

end tildeIdeal

/-- The quotient-map kernel datum is the affine ideal-sheaf datum induced from `I` on global
sections. -/
@[simp, stacks 01IG "affine quotient kernel datum"]
theorem quotientMap_ker (I : Ideal R) :
    (quotientMap I).ker = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso R).inv.hom) := sorry

/-- The ideal subobject represented by the quotient-map kernel datum is the explicit tilde ideal
subobject. -/
@[simp, stacks 01IG "affine quotient kernel subobject"]
theorem quotientMap_ker_toSubobject (I : Ideal R) :
    (quotientMap I).ker.toSubobject = tildeIdeal.subobject I := sorry

/-- The kernel ideal subobject of the quotient closed immersion is the explicit tilde ideal
subobject. -/
@[simp, stacks 01IG "affine quotient kernel ideal subobject"]
theorem quotientMap_kernelIdealSubobject (I : Ideal R) :
    LocallyRingedSpace.Hom.kernelIdealSubobject (quotientMap I).toLRSHom =
      tildeIdeal.subobject I := sorry

/-- The map `Spec (R ⧸ I) ⟶ Spec R` is the closed subspace associated to the
quasi-coherent ideal subobject represented by `Ĩ`. -/
@[stacks 01IG "affine quotient associated to tilde ideal"]
theorem quotientMap_isAssociated (I : Ideal R) :
    LocallyRingedSpace.ClosedSubspace.IsAssociated
      (quotientMap I).toLRSHom (tildeIdeal.subobject I) := sorry

/-- The affine quotient map is a closed immersion, so its scheme-theoretic image map is an
isomorphism. -/
@[stacks 01IG "affine quotient closed immersion", instance]
theorem quotientMap_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion (quotientMap I) := sorry

/-- The affine quotient is canonically isomorphic to the Mathlib closed subscheme attached to its
kernel ideal-sheaf datum. -/
@[stacks 01IG "affine quotient as canonical subscheme"]
noncomputable def quotientIsoSubscheme (I : Ideal R) :
    Spec (CommRingCat.of (R ⧸ I)) ≅ (quotientMap I).ker.subscheme :=
  asIso (quotientMap I).toImage

/-- The canonical affine quotient comparison is an isomorphism over `Spec R`. -/
@[reassoc (attr := simp), stacks 01IG "affine quotient subscheme comparison"]
theorem quotientIsoSubscheme_hom_subschemeι (I : Ideal R) :
    (quotientIsoSubscheme I).hom ≫ (quotientMap I).ker.subschemeι =
      quotientMap I := sorry

/-- The affine quotient and its canonical ideal-sheaf subscheme are isomorphic as objects over
`Spec R`. -/
@[stacks 01IG "affine quotient over isomorphism"]
noncomputable def quotientOverIso (I : Ideal R) :
    Over.mk (quotientMap I) ≅ Over.mk (quotientMap I).ker.subschemeι :=
  Over.isoMk (quotientIsoSubscheme I) (quotientIsoSubscheme_hom_subschemeι I)

end AlgebraicGeometry.Spec
