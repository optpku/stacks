/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.QuasiSeparated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On a quasi-separated scheme, a derived module with quasicoherent cohomology has
Tor-amplitude in `[a, b]` if and only if tensoring it with every quasicoherent module has
vanishing cohomology outside `[a, b]`. -/
theorem hasTorAmplitudeIn_iff_homology {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (a b : ℤ) (hab : a ≤ b) :
    RingedSpace.HasTorAmplitudeIn E.obj a b ↔
      ∀ (F : RingedSpace.QCoh X.toRingedSpace) (i : ℤ), i ∉ Set.Icc a b →
        IsZero (RingedSpace.ModuleDerived.cohomologySheaf
          (E.obj ⊗ᴸ
            (DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj F.obj) i) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
