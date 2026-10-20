/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeFiltration
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Coefficients
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Relative de Rham cohomology over an affine base

This module owns the canonical affine-base scalar map and the resulting module-valued relative
de Rham cohomology objects.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The canonical map from an affine base ring to the global sections of its inverse-image
coefficient sheaf on a scheme over that base. -/
noncomputable abbrev baseRingMapOfAffineTarget {A : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec A) :
    RingCat.of A ⟶ RingedSite.Hom.globalSectionsRing
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) :=
  (forget₂ CommRingCat RingCat).map
      ((ΓSpecIso A).inv ≫
        (ModuleCech.relativeSpaceMap p.toLRSHom.toShHom).hom.c.app (Opposite.op ⊤)) ≫
    ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) RingCat
      Limits.isTerminalTop).app
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom))).inv ≫
    ((Sheaf.ΓNatIsoLim (Opens.grothendieckTopology X) RingCat).app
      (TopCat.Sheaf.ringSheafOfComm
        (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom))).hom

/-- Relative de Rham cohomology over an affine base, with its natural module structure over the
base ring. -/
noncomputable abbrev cohomologyOverAffineBase {A : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec A) (i : ℤ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (baseRingMapOfAffineTarget p).hom).obj (cohomology p i)

end AlgebraicGeometry.Scheme.DeRham
