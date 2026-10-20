/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Dualizable
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Injective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ProjectionFormula

/-!
# Projection Formula for Higher Direct Images

The classical degreewise statement is exposed through a canonical natural transformation,
its invertibility, and the resulting natural isomorphism.  The construction specializes the
categorical projection formula for ordinary right derived functors.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage

/-- The canonical projection-formula transformation for higher direct images at a finite
locally free target-side tensor factor. -/
@[stacks 01E8 "(1), canonical higher-direct-image mate"]
noncomputable abbrev projectionFormulaNatTrans
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [E.IsFiniteLocallyFree] (q : ℕ) :
    higherDirectImageModuleFunctor f q ⋙ tensorLeft E ⟶
      tensorLeft ((pullback f).obj E) ⋙ higherDirectImageModuleFunctor f q :=
  CategoryTheory.Adjunction.RightDerived.projectionFormulaNatTrans
    (pullbackPushforwardAdjunction f) E q

/-- The canonical projection-formula transformation for higher direct images at a finite
locally free tensor factor is invertible. -/
@[stacks 01E8 "(1), canonical higher-direct-image mate is invertible"]
theorem isIso_projectionFormulaNatTrans
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [E.IsFiniteLocallyFree] (q : ℕ) :
    IsIso (projectionFormulaNatTrans f E q) := sorry

/-- Right derivation of an explicit underived projection-formula isomorphism for a morphism of
ringed spaces.  The explicit input prevents the inverse data from being extracted from a deferred
invertibility proof. -/
@[stacks 01E8 "(1), functorial higher direct images from underived data"]
noncomputable abbrev projectionFormulaNatIsoOf
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [E.IsFiniteLocallyFree]
    (e : (pushforward f) ⋙ tensorLeft E ≅ tensorLeft ((pullback f).obj E) ⋙ (pushforward f))
    (q : ℕ) :
    higherDirectImageModuleFunctor f q ⋙ tensorLeft E ≅
      tensorLeft ((pullback f).obj E) ⋙ higherDirectImageModuleFunctor f q :=
  CategoryTheory.Adjunction.RightDerived.projectionFormulaNatIsoOf
    (L := pullback f) (R := pushforward f) e q

/-- The forward map of the higher-direct-image projection-formula isomorphism is the
canonical derived mate. -/
@[simp]
theorem projectionFormulaNatIsoOf_hom
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [E.IsFiniteLocallyFree]
    (e : (pushforward f) ⋙ tensorLeft E ≅ tensorLeft ((pullback f).obj E) ⋙ (pushforward f))
    (he : e.hom = (pullbackPushforwardAdjunction f).projectionFormulaMateNatTrans E)
    (q : ℕ) :
    (projectionFormulaNatIsoOf f E e q).hom = projectionFormulaNatTrans f E q := sorry

/-- The objectwise projection-formula isomorphism for a finite locally free tensor factor. -/
@[stacks 01E8 "(1), objectwise higher direct images"]
noncomputable abbrev projectionFormulaIsoOf
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [E.IsFiniteLocallyFree]
    (e : (pushforward f) ⋙ tensorLeft E ≅ tensorLeft ((pullback f).obj E) ⋙ (pushforward f))
    (F : X.Modules) (q : ℕ) :
    E ⊗ higherDirectImageModule f F q ≅
      higherDirectImageModule f ((pullback f).obj E ⊗ F) q :=
  (projectionFormulaNatIsoOf f E e q).app F

/-- The forward objectwise projection-formula map is the component of the canonical natural
transformation. -/
@[simp]
theorem projectionFormulaIsoOf_hom
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [E.IsFiniteLocallyFree]
    (e : (pushforward f) ⋙ tensorLeft E ≅ tensorLeft ((pullback f).obj E) ⋙ (pushforward f))
    (he : e.hom = (pullbackPushforwardAdjunction f).projectionFormulaMateNatTrans E)
    (F : X.Modules) (q : ℕ) :
    (projectionFormulaIsoOf f E e F q).hom =
      (projectionFormulaNatTrans f E q).app F := sorry

/-- The existence-of-isomorphism form of the higher-direct-image projection formula. -/
@[stacks 01E8 "(1), IsIsomorphic corollary"]
theorem projectionFormula
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [E.IsFiniteLocallyFree] (F : X.Modules) (q : ℕ) :
    IsIsomorphic
      (E ⊗ higherDirectImageModule f F q)
      (higherDirectImageModule f ((pullback f).obj E ⊗ F) q) := sorry

end AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage
