/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.CohomologyDetection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Right
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Characterization
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.FlatCokernel
import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.TFAE
import ReasLib.CategoryTheory.Pretriangulated.Triangle.Split

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpace.Hom.IsFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A perfect derived module on a quasi-compact open subscheme of an affine scheme becomes the
restriction of a perfect derived module after adjoining a shifted finite locally free module. -/
theorem exists_finiteLocallyFree_biprod_extension {X U : Scheme.{u}} [IsAffine X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (E : RingedSpace.ModuleDerived U.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    ∃ (r : ℤ) (F : U.Modules) (hF : F.IsFiniteLocallyFree)
      (P : RingedSpace.ModuleDerived X.toRingedSpace)
      (e : (exactPullback j.toShHom).mapDerivedCategory.obj P ≅
        ((DerivedCategory.singleFunctor U.toRingedSpace.Modules 0).obj F)⟦-r⟧ ⊞ E),
      RingedSpace.ModuleDerived.IsPerfect P := sorry

/-- A morphism from the restriction of a perfect derived module to the restriction of an
arbitrary derived module over a quasi-compact open of an affine scheme factors through a
perfect tensor product whose map to the source becomes an isomorphism after restriction. -/
theorem exists_tensorFactorization_of_isPerfect {X U : Scheme.{u}} [IsAffine X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (E E' : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (hE : RingedSpace.ModuleDerived.IsPerfect E.obj)
    (α : (OpenImmersion.pullback j).obj E ⟶ (OpenImmersion.pullback j).obj E') :
    ∃ (I : DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
      (hI : RingedSpace.ModuleDerived.IsPerfect I.obj)
      (hEI : RingedSpace.ModuleDerived.IsPerfect (tensorObj E I).obj)
      (β : tensorObj E I ⟶ E) (γ : tensorObj E I ⟶ E'),
      IsIso ((OpenImmersion.pullback j).map β) ∧
        (OpenImmersion.pullback j).map β ≫ α =
          (OpenImmersion.pullback j).map γ := sorry

/-- If `F` is a perfect derived module on a quasi-compact open subscheme of an affine scheme,
then `F ⊞ F⟦1⟧` extends to a perfect derived module on the ambient scheme. -/
theorem exists_biprod_shift_extension_of_isPerfect {X U : Scheme.{u}} [IsAffine X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : RingedSpace.ModuleDerived U.toRingedSpace)
    (hF : RingedSpace.ModuleDerived.IsPerfect F) :
    ∃ (P : RingedSpace.ModuleDerived X.toRingedSpace)
      (e : (exactPullback j.toShHom).mapDerivedCategory.obj P ≅ F ⊞ F⟦(1 : ℤ)⟧),
      RingedSpace.ModuleDerived.IsPerfect P := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
