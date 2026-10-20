/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObjectOverAffineOpen

/-! # Objects over spectra through an affine open of the base -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver Functor

universe u

#check (AlgebraicGeometry.GroupoidsOver.ObjectOverAffineOpen :
  ∀ {S : Scheme.{u}}, GroupoidsOver S → Type (u + 1))

variable {S : Scheme.{u}} {X : GroupoidsOver S}

#check (ObjectOverAffineOpen.Hom :
  ObjectOverAffineOpen X → ObjectOverAffineOpen X → Type u)

#check (ObjectOverAffineOpen.algebraHom :
  ∀ ξ : ObjectOverAffineOpen X, ξ.base ⟶ CommRingCat.of ξ.carrier)

#check (DeformationSituation.OverAffine : ObjectOverAffineOpen X → Type (u + 1))

#check (Spectrum.ObjectOverSpec.toFiber :
  ∀ ξ : ObjectOverSpec X, X.p.Fiber (Over.mk ξ.toS))
