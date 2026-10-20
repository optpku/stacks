/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Truncation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open RingedSpace.ModuleDerived RingedSpace.Module.Derived
open scoped CartesianClosed DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (G E : Scheme.ModuleDerived.Quasicoherent X)
variable (hG_perfect : RingedSpace.ModuleDerived.IsPerfect G.obj)
variable (hG_generator : IsWeakGenerator G)

include hG_perfect hG_generator

/-- Boundedness below is equivalent to eventual vanishing of shifted morphisms from a
perfect weak generator. -/
theorem isBoundedBelow_iff_homShiftEventually :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj) := sorry

/-- Boundedness below is equivalent to eventual negative-degree Ext vanishing against a
perfect weak generator. -/
theorem isBoundedBelow_iff_extEventually :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj)) := sorry

section Monoidal

variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- Boundedness below is equivalent to boundedness below of the derived global internal Hom
from a perfect weak generator. -/
theorem isBoundedBelow_iff_globalHom :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((GlobalSections.toAbelian X.toRingedSpace).obj (G.obj ⟹ E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorCohomologyEventually :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
        IsZero ((GlobalSections.cohomologyFunctor X.toRingedSpace i).obj
          (MonoidalClosed.dual G.obj ⊗ E.obj)) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorGlobalSections :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((GlobalSections.toAbelian X.toRingedSpace).obj
          (MonoidalClosed.dual G.obj ⊗ E.obj)) := sorry

end Monoidal

/-- Boundedness below is equivalent to eventual vanishing of shifted morphisms from every
perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectHomShiftEventually :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj) := sorry

/-- Boundedness below is equivalent to eventual negative-degree Ext vanishing against every
perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectExtEventually :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj)) := sorry

section Monoidal

variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- Boundedness below is equivalent to boundedness below of the derived global internal Hom
from every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectGlobalHom :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⟹ E.obj)) := sorry

end Monoidal

section Tensor

variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorCohomologyEventually :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
            IsZero ((GlobalSections.cohomologyFunctor X.toRingedSpace i).obj
              (P ⊗ E.obj)) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorGlobalSections :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⊗ E.obj)) := sorry

end Tensor

section Monoidal

variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- A perfect weak generator detects boundedness below through shifted morphisms, Ext,
derived global internal Hom, dual-tensor hypercohomology and derived global sections; the
same criteria may equivalently be required of every perfect ambient derived module. -/
theorem boundedBelow_tfae :
    List.TFAE
      [ (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((GlobalSections.toAbelian X.toRingedSpace).obj (G.obj ⟹ E.obj))
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
          IsZero ((GlobalSections.cohomologyFunctor X.toRingedSpace i).obj
            (MonoidalClosed.dual G.obj ⊗ E.obj))
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((GlobalSections.toAbelian X.toRingedSpace).obj
            (MonoidalClosed.dual G.obj ⊗ E.obj))
      , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
          RingedSpace.ModuleDerived.IsPerfect P →
            ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
          RingedSpace.ModuleDerived.IsPerfect P →
            ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
          RingedSpace.ModuleDerived.IsPerfect P →
            (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
              ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⟹ E.obj))
      , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
          RingedSpace.ModuleDerived.IsPerfect P →
            ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
              IsZero ((GlobalSections.cohomologyFunctor X.toRingedSpace i).obj
                (P ⊗ E.obj))
      , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
          RingedSpace.ModuleDerived.IsPerfect P →
            (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
              ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⊗ E.obj))
      ] := sorry

end Monoidal

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable (G E : Scheme.ModuleDerived.Quasicoherent X)
variable (hG_perfect : RingedSpace.ModuleDerived.IsPerfect G.obj)
variable (hG_generator : IsWeakGenerator G)

include hG_perfect hG_generator

/-- A perfect weak generator detects boundedness above through eventual shifted-morphism and
Ext vanishing, derived global internal Hom, dual-tensor hypercohomology and derived global
sections; the same criteria may equivalently be required of every perfect ambient derived
module. -/
theorem boundedAbove_tfae :
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
      ] := sorry

/-- A perfect weak generator detects boundedness above exactly when its positive-degree Ext
groups into the object eventually vanish. -/
theorem boundedAbove_iff_extEventually :
    (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- A derived quasicoherent object is bounded above exactly when tensoring it with every
perfect ambient derived module has eventually vanishing global hypercohomology. -/
theorem boundedAbove_iff_perfectTensorCohomologyEventually
    (E : Scheme.ModuleDerived.Quasicoherent X) :
    (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ↔
      ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop,
            IsZero ((RingedSpace.moduleDerivedCohomologyFunctor X.toRingedSpace i).obj
              (P ⊗ E.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
