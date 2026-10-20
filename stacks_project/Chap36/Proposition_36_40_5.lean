/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BoundednessDetection

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open RingedSpace.ModuleDerived RingedSpace.Module.Derived
open scoped CartesianClosed DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Proposition 36.40.5: for a perfect weak generator `G` of `D_QCoh(𝒪_X)`, an object
`E` is bounded above if and only if the eventual shifted-Hom, Ext, derived-global-Hom,
dual-tensor hypercohomology, derived-global-sections, and corresponding universal
perfect-object criteria hold. -/
@[stacks 0GEN] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.boundedAbove_tfae :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      (G E : Scheme.ModuleDerived.Quasicoherent X)
      (_ : RingedSpace.ModuleDerived.IsPerfect G.obj) (_ : IsWeakGenerator G),
      List.TFAE
        [ (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj
        , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
        , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj))
        , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((GlobalSections.toAbelian X.toRingedSpace).obj (G.obj ⟹ E.obj))
        , ∀ᶠ i : ℤ in Filter.atTop,
            IsZero ((RingedSpace.moduleDerivedCohomologyFunctor X.toRingedSpace i).obj
              (MonoidalClosed.dual G.obj ⊗ E.obj))
        , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((GlobalSections.toAbelian X.toRingedSpace).obj
              (MonoidalClosed.dual G.obj ⊗ E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (P⟦-i⟧ ⟶ E.obj)
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
                ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⟹ E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              ∀ᶠ i : ℤ in Filter.atTop,
                IsZero ((RingedSpace.moduleDerivedCohomologyFunctor X.toRingedSpace i).obj
                  (P ⊗ E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
                ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⊗ E.obj))
        ])

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.boundedAbove_iff_extEventually :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      (G E : Scheme.ModuleDerived.Quasicoherent X)
      (_ : RingedSpace.ModuleDerived.IsPerfect G.obj) (_ : IsWeakGenerator G),
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
        ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj)))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.boundedAbove_iff_perfectTensorCohomologyEventually :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      (E : Scheme.ModuleDerived.Quasicoherent X),
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
        ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
          RingedSpace.ModuleDerived.IsPerfect P →
            ∀ᶠ i : ℤ in Filter.atTop,
              IsZero ((RingedSpace.moduleDerivedCohomologyFunctor X.toRingedSpace i).obj
                (P ⊗ E.obj)))

end AlgebraicGeometry.Scheme.DerivedQCoh
