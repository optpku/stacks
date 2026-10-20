module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a quasi-compact and quasi-separated scheme, the derived coherator has uniformly
bounded cohomological amplitude on complexes whose affine-open hypercohomology is bounded. -/
theorem rightAdjoint_bounds_of_affineHypercohomology
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ N : ℤ, ∀ (K : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ),
      (∀ (U : X.Opens), IsAffineOpen U → ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U K i)) →
      ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj.IsGE a ∧
        ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj.IsLE (b + N) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
