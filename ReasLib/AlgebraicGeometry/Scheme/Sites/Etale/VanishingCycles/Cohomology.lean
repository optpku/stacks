/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.Cospecialization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Sections

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.EtaleVanishingCycles
open DerivedCategory.TStructure Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleVanishingCycles

variable {X S : Scheme.{u}} (f : X ⟶ S) (sbar : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk sbar.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar Rsh))
variable (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
variable (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom)

/-- Restriction of `K` to the henselized fibre `Xsh`. -/
abbrev restrictToHenselizedFiber (K : Complexes X) :
    Complexes (henselizedFiber f sbar Rsh) :=
  (derivedInverseImage (henselizedFiberToX f sbar Rsh)).obj K

/-- Restriction of `K` to the geometric fibre `X_tbar`. -/
abbrev restrictToGeometricFiberT (K : Complexes X) :
    Complexes
      (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom) :=
  (derivedInverseImage (cospecializationH f sbar Rsh tbar)).obj
    (restrictToHenselizedFiber f sbar Rsh K)

/-- Restriction of `K` to the geometric fibre `X_sbar`. -/
abbrev restrictToGeometricFiberS (K : Complexes X) :
    Complexes (pullback f sbar.hom) :=
  (derivedInverseImage (geometricFiberToHenselized f sbar Rsh iS hiS)).obj
    (restrictToHenselizedFiber f sbar Rsh K)

/-- Derived sections `RΓ(Xsh, K|_{Xsh})` on the henselized fibre. -/
def henselizedFiberSections (K : Complexes X) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (derivedSections (henselizedFiber f sbar Rsh)).obj
    (restrictToHenselizedFiber f sbar Rsh K)

/-- Derived sections `RΓ(Xsh, Rh_*(K|_{X_tbar}))` of the generic-fibre direct image. -/
def directImageFiberSections (K : Complexes X) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (derivedSections (henselizedFiber f sbar Rsh)).obj
    ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
      (restrictToGeometricFiberT f sbar Rsh tbar K))

/-- The map `RΓ(β)` representing specialization followed by generic-fibre comparison
in the strict-henselian reduction. -/
def derivedPushforwardSpecialization (K : Complexes X) :
    henselizedFiberSections f sbar Rsh K ⟶ directImageFiberSections f sbar Rsh tbar K :=
  (derivedSections (henselizedFiber f sbar Rsh)).map
    (etaleCohomologyBeta f sbar Rsh tbar K)

/-- The reduced cohomology map is derived sections of the adjunction comparison `β`. -/
theorem derivedPushforwardSpecialization_eq (K : Complexes X) :
    derivedPushforwardSpecialization f sbar Rsh tbar K =
      (derivedSections (henselizedFiber f sbar Rsh)).map
        (etaleCohomologyBeta f sbar Rsh tbar K) :=
  rfl

/-- Derived sections of the cochain-model direct image identify with sections on its domain. -/
def derivedSectionsDirectImageIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    derivedDirectImage g ⋙ derivedSections Z ≅ derivedSections Y :=
  Functor.isoWhiskerRight
      (Functor.rightDerivedUnique (derivedDirectImage g) (Etale.Derived.directImage g)
        (@Cochain.unit _ _ _ _ _ _ _ _ (Etale.Abelian.directImage g) inferInstance
          (Cochain.hasDerived.{u + 1} (Etale.Abelian.directImage g)))
        (Adjunction.Derived.KInjective.rightUnit (Etale.Abelian.directImage g))
        (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ)))
      (derivedSections Z) ≪≫
    Etale.Derived.directImageSectionsIso g

variable (K : Complexes X) (hK : t.plus K) [LocallyAcyclicRelative f K]

/-- The inverse of the closed-fibre restriction of the adjunction comparison. -/
def inverseImageBetaInv :
    (derivedInverseImage (geometricFiberToHenselized f sbar Rsh iS hiS)).obj
        ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
          (restrictToGeometricFiberT f sbar Rsh tbar K)) ⟶
      restrictToGeometricFiberS f sbar Rsh iS hiS K :=
  @CategoryTheory.inv _ _ _ _
    ((derivedInverseImage (geometricFiberToHenselized f sbar Rsh iS hiS)).map
      (etaleCohomologyBeta f sbar Rsh tbar K))
    (isIso_inverseImage_etaleCohomologyBeta f sbar Rsh tbar iS hiS K hK)

/-- The cospecialization map `cosp : RΓ(X_tbar, K) ⟶ RΓ(X_sbar, K)`. -/
def cospecializationMap :
    (derivedSections
        (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom)).obj
      (restrictToGeometricFiberT f sbar Rsh tbar K) ⟶
      (derivedSections (pullback f sbar.hom)).obj
        (restrictToGeometricFiberS f sbar Rsh iS hiS K) :=
  (derivedSectionsDirectImageIso (cospecializationH f sbar Rsh tbar)).inv.app
      (restrictToGeometricFiberT f sbar Rsh tbar K) ≫
    (derivedSectionsPullback (geometricFiberToHenselized f sbar Rsh iS hiS)).app
      ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
        (restrictToGeometricFiberT f sbar Rsh tbar K)) ≫
    (derivedSections (pullback f sbar.hom)).map
      (inverseImageBetaInv f sbar Rsh tbar iS hiS K hK)

/-- Cospecialization inverts `RΓ(Xsh, Rh_*) ≅ RΓ(X_tbar)`, pulls back along `i`,
and applies the inverse of `i⁻¹ β`. -/
theorem cospecializationMap_eq :
    cospecializationMap f sbar Rsh tbar iS hiS K hK =
      (derivedSectionsDirectImageIso (cospecializationH f sbar Rsh tbar)).inv.app
          (restrictToGeometricFiberT f sbar Rsh tbar K) ≫
        (derivedSectionsPullback (geometricFiberToHenselized f sbar Rsh iS hiS)).app
          ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
            (restrictToGeometricFiberT f sbar Rsh tbar K)) ≫
        (derivedSections (pullback f sbar.hom)).map
          (inverseImageBetaInv f sbar Rsh tbar iS hiS K hK) :=
  rfl

end AlgebraicGeometry.Scheme.EtaleVanishingCycles
