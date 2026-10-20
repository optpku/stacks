/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.Cospecialization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.DirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Sections

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleVanishingCycles

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale.Cohomology

variable {X S : Scheme.{u}} (f : X ⟶ S) (s t : GeometricPoint S)
variable (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
variable (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)

/-- A geometric fibre lying over a point of the strict henselization maps to the
strict-henselian base change. -/
def fiberToStrictHenselization :
    pullback f t.hom ⟶ pullback f (StrictHenselization.toScheme S s) :=
  pullback.lift (pullback.fst f t.hom) (pullback.snd f t.hom ≫ point)
    ((pullback.condition (f := f) (g := t.hom)).trans
      ((congrArg (fun g => pullback.snd f t.hom ≫ g) point_over.symm).trans
        (Category.assoc _ _ _).symm))

/-- The geometric-fibre inclusion preserves projection to the original scheme. -/
theorem fiberToStrictHenselization_fst :
    fiberToStrictHenselization f s t point point_over ≫
        pullback.fst f (StrictHenselization.toScheme S s) = pullback.fst f t.hom := sorry

/-- Iterated restriction through the strict-henselian base change identifies with
restriction to the direct geometric fibre. -/
def fiberInverseImageIso :
    Derived.inverseImage (pullback.fst f (StrictHenselization.toScheme S s)) ⋙
        Derived.inverseImage (fiberToStrictHenselization f s t point point_over) ≅
      Derived.inverseImage (pullback.fst f t.hom) :=
  (Derived.inverseImageCompIso (fiberToStrictHenselization f s t point point_over)
    (pullback.fst f (StrictHenselization.toScheme S s))).symm ≪≫
    eqToIso (congrArg (fun g => Derived.inverseImage g)
      (fiberToStrictHenselization_fst f s t point point_over))

/-- The adjunction unit compares coefficients on the strict-henselian base change
with the derived direct image of their restriction to the geometric fibre. -/
def cospecializationBeta (K : Complexes X) :
    (Derived.inverseImage (pullback.fst f (StrictHenselization.toScheme S s))).obj K ⟶
      (Derived.directImage (fiberToStrictHenselization f s t point point_over)).obj
        ((Derived.inverseImage (pullback.fst f t.hom)).obj K) :=
  (Derived.adjunction (fiberToStrictHenselization f s t point point_over)).unit.app
      ((Derived.inverseImage (pullback.fst f (StrictHenselization.toScheme S s))).obj K) ≫
    (Derived.directImage (fiberToStrictHenselization f s t point point_over)).map
      ((fiberInverseImageIso f s t point point_over).hom.app K)

/-- Relative local acyclicity makes the closed-fibre restriction of the adjunction
comparison invertible for bounded-below coefficients. -/
instance closedFiberBeta_isIso (K : DerivedCategory.Plus (Coefficients X))
    [LocallyAcyclicRelative f K.obj] :
    IsIso ((Derived.inverseImage
      (fiberToStrictHenselization f s s (StrictHenselization.closedPoint s)
        (StrictHenselization.closedPoint_over s))).map
      (cospecializationBeta f s t point point_over K.obj)) := sorry

/-- Cospecialization on geometric-fibre cohomology is restriction from the derived
direct image followed by the inverse of the closed-fibre comparison. -/
def cospecialization (K : DerivedCategory.Plus (Coefficients X))
    [LocallyAcyclicRelative f K.obj] :
    (derivedSections (pullback f t.hom)).obj
        ((Derived.inverseImage (pullback.fst f t.hom)).obj K.obj) ⟶
      (derivedSections (pullback f s.hom)).obj
        ((Derived.inverseImage (pullback.fst f s.hom)).obj K.obj) :=
  let h := fiberToStrictHenselization f s t point point_over
  let i := fiberToStrictHenselization f s s (StrictHenselization.closedPoint s)
    (StrictHenselization.closedPoint_over s)
  let betaIso := @asIso _ _ _ _
    ((Derived.inverseImage i).map (cospecializationBeta f s t point point_over K.obj))
    (closedFiberBeta_isIso f s t point point_over K)
  (Derived.directImageSectionsIso h).inv.app
      ((Derived.inverseImage (pullback.fst f t.hom)).obj K.obj) ≫
    (Derived.sectionsPullback i).app
      ((Derived.directImage h).obj
        ((Derived.inverseImage (pullback.fst f t.hom)).obj K.obj)) ≫
    (derivedSections (pullback f s.hom)).map
      (betaIso.inv ≫ (fiberInverseImageIso f s s (StrictHenselization.closedPoint s)
        (StrictHenselization.closedPoint_over s)).hom.app K.obj)

/-- Cospecialization is the inverse direct-image sections comparison, closed-fibre
restriction, and the inverse restricted adjunction comparison with coefficient transport. -/
theorem cospecialization_eq (K : DerivedCategory.Plus (Coefficients X))
    [LocallyAcyclicRelative f K.obj] :
    cospecialization f s t point point_over K =
      (Derived.directImageSectionsIso
        (fiberToStrictHenselization f s t point point_over)).inv.app
          ((Derived.inverseImage (pullback.fst f t.hom)).obj K.obj) ≫
      (Derived.sectionsPullback (fiberToStrictHenselization f s s
        (StrictHenselization.closedPoint s) (StrictHenselization.closedPoint_over s))).app
          ((Derived.directImage (fiberToStrictHenselization f s t point point_over)).obj
            ((Derived.inverseImage (pullback.fst f t.hom)).obj K.obj)) ≫
      (derivedSections (pullback f s.hom)).map
        ((@asIso _ _ _ _
          ((Derived.inverseImage (fiberToStrictHenselization f s s
            (StrictHenselization.closedPoint s) (StrictHenselization.closedPoint_over s))).map
              (cospecializationBeta f s t point point_over K.obj))
          (closedFiberBeta_isIso f s t point point_over K)).inv ≫
          (fiberInverseImageIso f s s (StrictHenselization.closedPoint s)
            (StrictHenselization.closedPoint_over s)).hom.app K.obj) := sorry

end AlgebraicGeometry.Scheme.Etale.Cohomology

namespace AlgebraicGeometry.Scheme

/-- For a quasi-compact quasi-separated morphism locally acyclic relative to bounded-below
coefficients, geometric stalk specialization and geometric-fibre cospecialization commute
with the canonical base-change maps. -/
theorem etaleCohomologyCospecialization_commSq
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (s t : GeometricPoint S) (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj] :
    Etale.Cohomology.etaleStalkToGeometricFiberBaseChange f s K.obj =
      Etale.derivedPushforward_specializationMap f s t point point_over K.obj ≫
        Etale.Cohomology.etaleStalkToGeometricFiberBaseChange f t K.obj ≫
          Etale.Cohomology.cospecialization f s t point point_over K := sorry

end AlgebraicGeometry.Scheme
