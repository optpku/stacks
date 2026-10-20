/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Pullback

/-! # Cohomology transitions between affine base changes -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {X : Scheme.{u}}

/-- The cohomology transition for a map of base algebras is geometric pullback followed
by the canonical identification of the pulled-back coefficients with the direct base change. -/
def affineBaseChangeCohomologyMap (f : X ⟶ Spec (CommRingCat.of A)) (ℱ : X.Modules)
    (g : B →ₐ[A] C) (i : ℕ)
    (x : Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase A B f)
      (AffineBaseChange.baseChange A B f ℱ) i) :
    Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase A C f)
      (AffineBaseChange.baseChange A C f ℱ) i :=
  (Scheme.Hom.cohomologyFunctor (Scheme.AffineBaseChange.toBase A C f) i).map
    (((pullbackComp (Scheme.AffineBaseChange.mapAlg f g)
        (Scheme.AffineBaseChange.toSource A B f)).hom.app ℱ) ≫
      (pullbackCongr (Scheme.AffineBaseChange.mapAlg_toSource f g)).hom.app ℱ)
    (Scheme.Hom.cohomologyPullback (Scheme.AffineBaseChange.toBase A B f)
      (Scheme.AffineBaseChange.mapAlg f g) (AffineBaseChange.baseChange A B f ℱ) i x)

/-- The affine base-change transition factors as pullback of classes and the cohomology
map of the canonical coefficient identification. -/
theorem affineBaseChangeCohomologyMap_apply
    (f : X ⟶ Spec (CommRingCat.of A)) (ℱ : X.Modules) (g : B →ₐ[A] C) (i : ℕ)
    (x : Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase A B f)
      (AffineBaseChange.baseChange A B f ℱ) i) :
    affineBaseChangeCohomologyMap f ℱ g i x =
      (Scheme.Hom.cohomologyFunctor (Scheme.AffineBaseChange.toBase A C f) i).map
        (((pullbackComp (Scheme.AffineBaseChange.mapAlg f g)
            (Scheme.AffineBaseChange.toSource A B f)).hom.app ℱ) ≫
          (pullbackCongr (Scheme.AffineBaseChange.mapAlg_toSource f g)).hom.app ℱ)
        (Scheme.Hom.cohomologyPullback (Scheme.AffineBaseChange.toBase A B f)
          (Scheme.AffineBaseChange.mapAlg f g) (AffineBaseChange.baseChange A B f ℱ) i x) := rfl

end AlgebraicGeometry.Scheme.Modules
