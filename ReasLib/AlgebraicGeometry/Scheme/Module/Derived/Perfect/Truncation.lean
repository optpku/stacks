module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.CohomologyDetection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a perfect derived module on a quasi-compact quasi-separated scheme, eventual
vanishing of negative-degree Ext into a derived quasicoherent object is equivalent to
eventual vanishing after any upper truncation of the target. -/
theorem extSubsingletonEventually_iff_truncLE {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {P : RingedSpace.ModuleDerived X.toRingedSpace}
    (hP : RingedSpace.ModuleDerived.IsPerfect P)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (a : ℤ) :
    (∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
        Subsingleton (Ext⁽i⁾(P, (t.truncLE a).obj E.obj)) := sorry

/-- For a perfect derived module on a quasi-compact quasi-separated scheme, eventual
vanishing of positive-degree Ext into a derived quasicoherent object is equivalent to
eventual vanishing after any lower truncation of the target. -/
theorem extSubsingletonEventually_iff_truncGE {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {P : RingedSpace.ModuleDerived X.toRingedSpace}
    (hP : RingedSpace.ModuleDerived.IsPerfect P)
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X) (a : ℤ) :
    (∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
      ∀ᶠ i : ℤ in Filter.atTop,
        Subsingleton (Ext⁽i⁾(P, (t.truncGE a).obj E.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
