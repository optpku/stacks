/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PerfectApproximation

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme admits approximation by perfect complexes if every closed subset with
retrocompact complement has a uniform loss of pseudo-coherence after which supported
quasicoherent derived objects have perfect approximations. -/
def HasApproximationByPerfectComplexes (X : Scheme.{u}) : Prop :=
  ∀ T : TopologicalSpace.Closeds X, IsRetrocompact ((T : Set X)ᶜ) →
    ∃ r : ℤ,
      ∀ (E : DerivedCategory.CohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ),
        RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj (m - r) →
          (∀ i : ℤ, m - r ≤ i →
            RingedSpace.moduleSupportedOn (T : Set X)
              (RingedSpace.ModuleDerived.cohomologySheaf E.obj i)) →
            HasPerfectApproximation T E m

/-- The quantified characterization of approximation by perfect complexes on a scheme. -/
theorem hasApproximationByPerfectComplexes_iff (X : Scheme.{u}) :
    HasApproximationByPerfectComplexes X ↔
      ∀ T : TopologicalSpace.Closeds X, IsRetrocompact ((T : Set X)ᶜ) →
        ∃ r : ℤ,
          ∀ (E : DerivedCategory.CohomologyIn
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ),
            RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj (m - r) →
              (∀ i : ℤ, m - r ≤ i →
                RingedSpace.moduleSupportedOn (T : Set X)
                  (RingedSpace.ModuleDerived.cohomologySheaf E.obj i)) →
                HasPerfectApproximation T E m := sorry

namespace HasApproximationByPerfectComplexes

/-- Approximation by perfect complexes supplies a uniform pseudo-coherence shift for each
closed subset with retrocompact complement. -/
theorem existsShift {X : Scheme.{u}} (hX : HasApproximationByPerfectComplexes X)
    (T : TopologicalSpace.Closeds X) (hT : IsRetrocompact ((T : Set X)ᶜ)) :
    ∃ r : ℤ,
      ∀ (E : DerivedCategory.CohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ),
        RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj (m - r) →
          (∀ i : ℤ, m - r ≤ i →
            RingedSpace.moduleSupportedOn (T : Set X)
              (RingedSpace.ModuleDerived.cohomologySheaf E.obj i)) →
            HasPerfectApproximation T E m := sorry

end HasApproximationByPerfectComplexes

end AlgebraicGeometry.Scheme
