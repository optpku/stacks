/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Products

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On the affine line over `ℤ`, the source of the uncoherated sheafy trace comparison
has quasicoherent cohomology. -/
theorem affineLineTraceSourceMem :
    let Y := Spec (CommRingCat.of ℤ)
    let X := Spec (CommRingCat.of (Polynomial ℤ))
    let f : X ⟶ Y := Spec.map (CommRingCat.ofHom Polynomial.C)
    let L := structureSheaf X
    let K := structureSheaf Y
    ∀ [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a),
      derivedQuasiCoherentModuleProperty Y
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((ihom L.obj).obj (a.obj K).obj)) := sorry

/-- On the affine line over `ℤ`, the target of the uncoherated sheafy trace comparison
is isomorphic to a countable product of copies of the base structure sheaf. -/
theorem affineLineTraceTargetIsoProduct :
    let Y := Spec (CommRingCat.of ℤ)
    let X := Spec (CommRingCat.of (Polynomial ℤ))
    let f : X ⟶ Y := Spec.map (CommRingCat.ofHom Polynomial.C)
    let L := structureSheaf X
    let K := structureSheaf Y
    ∀ [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)],
      IsIsomorphic
        ((ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).obj K.obj)
        (∏ᶜ fun _ : ℕ ↦ K.obj) := sorry

/-- The countable product of copies of the structure sheaf on `Spec ℤ` does not have
quasicoherent cohomology. -/
theorem countableProductStructureSheafNotQuasicoherent :
    let Y := Spec (CommRingCat.of ℤ)
    let K := structureSheaf Y
    ¬ derivedQuasiCoherentModuleProperty Y (∏ᶜ fun _ : ℕ ↦ K.obj) := sorry

/-- The uncoherated sheafy trace comparison for the affine line over `ℤ` is not an
isomorphism. -/
theorem affineLineTraceMapNotIso :
    let Y := Spec (CommRingCat.of ℤ)
    let X := Spec (CommRingCat.of (Polynomial ℤ))
    let f : X ⟶ Y := Spec.map (CommRingCat.ofHom Polynomial.C)
    let L := structureSheaf X
    let K := structureSheaf Y
    ∀ [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a),
      ¬ IsIso (uncoheratedSheafyTraceMap f a adj L K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
