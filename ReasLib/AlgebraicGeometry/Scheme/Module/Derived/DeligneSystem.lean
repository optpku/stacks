/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Filtration
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.InverseSystem.Positive
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Deligne systems of ideal-power complexes

This module packages the positive ideal-power tower of a bounded termwise coherent complex,
together with its chosen constant restriction along an open immersion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IdealPowerComplex

variable {X : Scheme.{u}}

/-- An inequality of positive natural indices induces the corresponding inequality of integer
filtration indices. -/
theorem pnatCast_le {m n : ℕ+} (h : m ≤ n) :
    (((m : ℕ) : ℤ) ≤ ((n : ℕ) : ℤ)) := sorry

/-- The identity law for the explicit positive ideal-power stage assignment. -/
theorem positiveCochainSystem_map_id (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (n : OrderDual ℕ+) :
    HomologicalComplex.Filtered.Stage.comparison (filtered I K)
        (pnatCast_le (𝟙 n).le) =
      𝟙 (HomologicalComplex.Filtered.Stage.complex (filtered I K)
        (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ)) := sorry

/-- The composition law for the explicit positive ideal-power stage assignment. -/
theorem positiveCochainSystem_map_comp (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) {i j k : OrderDual ℕ+}
    (f : i ⟶ j) (g : j ⟶ k) :
    HomologicalComplex.Filtered.Stage.comparison (filtered I K)
        (pnatCast_le (f ≫ g).le) =
      HomologicalComplex.Filtered.Stage.comparison (filtered I K)
          (pnatCast_le f.le) ≫
        HomologicalComplex.Filtered.Stage.comparison (filtered I K)
          (pnatCast_le g.le) := sorry

/-- The positive inverse system whose stage `n` is the explicit termwise ideal-power complex
`I ^ n K`. -/
noncomputable def positiveCochainSystem (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) :
    PNatInverseSystem (CochainComplex X.Modules ℤ) where
  obj n := HomologicalComplex.Filtered.Stage.complex (filtered I K)
    (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ)
  map f := HomologicalComplex.Filtered.Stage.comparison (filtered I K)
    (pnatCast_le f.le)
  map_id n := positiveCochainSystem_map_id I K n
  map_comp f g := positiveCochainSystem_map_comp I K f g

/-- The stage of `positiveCochainSystem` is the corresponding explicit filtration-stage
complex. -/
theorem positiveCochainSystem_stage (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (n : ℕ+) :
    (positiveCochainSystem I K).stage n =
      HomologicalComplex.Filtered.Stage.complex (filtered I K) (((n : ℕ) : ℤ)) := sorry

/-- A transition of `positiveCochainSystem` is the canonical inclusion between the two
ideal-power stages. -/
theorem positiveCochainSystem_transitionMap (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) {m n : ℕ+} (h : m ≤ n) :
    OrderDualInverseSystem.transitionMap (positiveCochainSystem I K) h =
      HomologicalComplex.Filtered.Stage.comparison (filtered I K) (pnatCast_le h) := sorry

/-- The positive ideal-power system after localization to the derived category. -/
noncomputable def positiveDerivedSystem (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) : PNatInverseSystem (DerivedCategory X.Modules) :=
  positiveCochainSystem I K ⋙ DerivedCategory.Q

/-- The stage of the positive derived system is the localized ideal-power stage. -/
theorem positiveDerivedSystem_stage (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (n : ℕ+) :
    (positiveDerivedSystem I K).stage n =
      DerivedCategory.Q.obj
        (HomologicalComplex.Filtered.Stage.complex (filtered I K) (((n : ℕ) : ℤ))) := sorry

/-- A transition of the positive derived system is the localization of the corresponding
ideal-power inclusion. -/
theorem positiveDerivedSystem_transitionMap (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) {m n : ℕ+} (h : m ≤ n) :
    OrderDualInverseSystem.transitionMap (positiveDerivedSystem I K) h =
      DerivedCategory.Q.map
        (HomologicalComplex.Filtered.Stage.comparison (filtered I K) (pnatCast_le h)) := sorry

end AlgebraicGeometry.Scheme.Modules.IdealPowerComplex

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A Deligne system presented by powers of an ideal acting on a bounded termwise coherent
complex, with a chosen identification of its restriction with a constant bounded coherent
derived object. -/
structure DeligneSystem
    {X U : Scheme.{v}} (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j] where
  /-- The ideal cutting out the complement of the open immersion. -/
  ideal : X.IdealSheafData
  /-- A bounded complex whose terms are coherent module sheaves. -/
  complex : CochainComplex.BoundedTermsIn
    (SheafOfModules.isCoherent X.ringCatSheaf)
  /-- The ideal support complement is exactly the range of the open immersion. -/
  openComplement_eq : ideal.openComplement = j.opensRange
  /-- The value of the restricted constant system in the bounded coherent derived category. -/
  value : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]
  /-- The chosen natural identification of the restricted ideal-power tower with the constant
  tower at `value`. -/
  restrictionIso :
    Modules.IdealPowerComplex.positiveDerivedSystem ideal complex.obj ⋙
        RingedSpace.modulePullbackDerived j.toShHom ≅
      (Functor.const (OrderDual ℕ+)).obj
        ((DerivedCategory.Bounded.CohomologyIn.ambient
          (SheafOfModules.isCoherent U.ringCatSheaf)).obj value)

namespace DeligneSystem

universe v

variable {X U : Scheme.{v}} (j : U ⟶ X)
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- Construct a Deligne system from an ideal-power presentation and its explicit constant
restriction identification. -/
noncomputable def ofIdealPower
    (ideal : X.IdealSheafData)
    (complex : CochainComplex.BoundedTermsIn
      (SheafOfModules.isCoherent X.ringCatSheaf))
    (openComplement_eq : ideal.openComplement = j.opensRange)
    (value : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (restrictionIso :
      Modules.IdealPowerComplex.positiveDerivedSystem ideal complex.obj ⋙
          RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((DerivedCategory.Bounded.CohomologyIn.ambient
            (SheafOfModules.isCoherent U.ringCatSheaf)).obj value)) :
    DeligneSystem j where
  ideal := ideal
  complex := complex
  openComplement_eq := openComplement_eq
  value := value
  restrictionIso := restrictionIso

/-- The ideal-power presentation used by a Deligne system determines its support complement
and is termwise coherent. -/
theorem spec (S : DeligneSystem j) :
    S.ideal.openComplement = j.opensRange ∧
      ∀ i : ℤ, SheafOfModules.isCoherent X.ringCatSheaf (S.complex.obj.X i) := sorry

/-- The explicit positive derived ideal-power tower underlying a Deligne system. -/
noncomputable def tower (S : DeligneSystem j) :
    PNatInverseSystem (DerivedCategory X.Modules) :=
  Modules.IdealPowerComplex.positiveDerivedSystem S.ideal S.complex.obj

/-- The tower of a Deligne system is its presented positive ideal-power system. -/
theorem tower_eq (S : DeligneSystem j) :
    S.tower = Modules.IdealPowerComplex.positiveDerivedSystem
      S.ideal S.complex.obj := sorry

/-- The derived object at positive stage `n` of a Deligne system. -/
noncomputable def stage (S : DeligneSystem j) (n : ℕ+) : DerivedCategory X.Modules :=
  S.tower.stage n

/-- A Deligne-system stage is the localization of the corresponding explicit filtered complex. -/
theorem stage_eq (S : DeligneSystem j) (n : ℕ+) :
    DeligneSystem.stage j S n = DerivedCategory.Q.obj
      (HomologicalComplex.Filtered.Stage.complex
        (Modules.IdealPowerComplex.filtered S.ideal S.complex.obj) (((n : ℕ) : ℤ))) := sorry

end DeligneSystem

end AlgebraicGeometry.Scheme.ModuleDerived
