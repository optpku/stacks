/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.Affine

/-!
# Compatibility checks for big h sites over a scheme

This module preserves the historical import path for the chosen big h-site
and affine big h-site constructions.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {P : Precoverage AlgebraicGeometry.Scheme.{u}}

#check (AlgebraicGeometry.ChosenBigSite.affineSite :
  (X : AlgebraicGeometry.ChosenBigSite.{u, v} P) →
    (S : X.carrier) → Type (max u v))

#check (AlgebraicGeometry.ChosenBigSite.affineInclusion :
  (X : AlgebraicGeometry.ChosenBigSite.{u, v} P) →
    (S : X.carrier) → AlgebraicGeometry.ChosenBigSite.affineSite X S ⥤ Over S)

#check (AlgebraicGeometry.ChosenBigSite.affineToScheme :
  (X : AlgebraicGeometry.ChosenBigSite.{u, v} P) →
    (S : X.carrier) →
      AlgebraicGeometry.ChosenBigSite.affineSite X S ⥤ AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.ChosenBigHSite.bigTopology :
  (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) →
    (S : X.carrier) → GrothendieckTopology (Over S))

#check (AlgebraicGeometry.ChosenBigHSite.bigAffineStandardPrecoverage :
  (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) →
    (S : X.carrier) →
      Precoverage (AlgebraicGeometry.ChosenBigSite.affineSite X S))

#check (AlgebraicGeometry.ChosenBigHSite.bigAffineTopology :
  (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) →
    (S : X.carrier) →
      GrothendieckTopology (AlgebraicGeometry.ChosenBigSite.affineSite X S))
