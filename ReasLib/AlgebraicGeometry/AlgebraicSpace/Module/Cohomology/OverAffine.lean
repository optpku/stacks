module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import Mathlib.CategoryTheory.IsomorphismClasses

/-! # Cohomology over an affine base -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open Opposite TopCat TopologicalSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for definitional equality of higher direct images.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Cohomology `H^i(X, ℱ)` as an `A`-module, realized as global sections of the scheme-module
image of `R^i f_* ℱ` on `Spec A`. -/
def cohomologyOver {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) (i : ℕ) :
    ModuleCat A :=
  (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
    ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i))

/-- `cohomologyOver` is global sections of `toScheme` of the higher direct image. -/
theorem cohomologyOver_eq {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) (i : ℕ) :
    cohomologyOver σA f ℱ i =
      (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i)) :=
  rfl

/-- Affine-base cohomology, after forgetting scalars, is étale sheaf cohomology for a
quasi-coherent module under a quasi-compact and quasi-separated structure morphism. -/
theorem cohomologyOver_forget_isIsomorphic {A : Type u} [CommRing A]
    {X : AlgebraicSpace S} (σA : Spec (CommRingCat.of A) ⟶ S)
    (f : X ⟶ ofOver (Over.mk σA)) [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic ((forget₂ (ModuleCat A) AddCommGrpCat).obj (cohomologyOver σA f ℱ i))
      (AlgebraicGeometry.AlgebraicSpace.cohomology X ℱ i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
