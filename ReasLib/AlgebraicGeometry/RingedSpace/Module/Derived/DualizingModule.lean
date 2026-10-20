/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Dualizing

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

/-- A sheaf `M` is the dualizing module cut out by a dualizing complex `K` in degree `n`
when it is the coherent, nonzero degree-`n` cohomology sheaf and all lower cohomology vanishes. -/
structure IsDualizingModule {X : RingedSpace.{u}} (K : ModuleDerived X)
    [MonoidalCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) (n : ℤ) (M : X.Modules) : Prop where
  ofFields ::
  /-- The ambient complex is dualizing. -/
  complexIsDualizing : IsDualizingComplex K H
  /-- The module is the degree-`n` cohomology sheaf. -/
  eqCohomology : M = cohomologySheaf K n
  /-- The dualizing module is coherent. -/
  coherent : M.IsCoherent
  /-- All cohomology below degree `n` vanishes. -/
  vanishesBelow : ∀ i : ℤ, i < n → IsZero (cohomologySheaf K i)
  /-- The degree-`n` cohomology sheaf is nonzero. -/
  leftmostNonzero : ¬ IsZero M

namespace IsDualizingModule

-- Local declaration justification (localized automation): companion constructor for a Prop
-- structure must be a `def` rather than a `theorem`.
set_option linter.defProp false

/-- Assemble the dualizing-module predicate from a dualizing complex, a cohomology identification
in degree `n`, coherence, vanishing below that degree, and nonvanishing of the module. -/
def mk {X : RingedSpace.{u}} (K : ModuleDerived X)
    [MonoidalCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) (n : ℤ) (M : X.Modules)
    (complexIsDualizing : IsDualizingComplex K H)
    (eqCohomology : M = cohomologySheaf K n)
    (coherent : M.IsCoherent)
    (vanishesBelow : ∀ i : ℤ, i < n → IsZero (cohomologySheaf K i))
    (leftmostNonzero : ¬ IsZero M) :
    IsDualizingModule K H n M :=
  { complexIsDualizing, eqCohomology, coherent, vanishesBelow, leftmostNonzero }

/-- Construct a dualizing module from a dualizing complex and its coherent leftmost nonzero
cohomology sheaf. -/
theorem ofLeftmostCohomology {X : RingedSpace.{u}} {K : ModuleDerived X}
    [MonoidalCategory (ModuleDerived X)]
    {H : MonoidalClosed (ModuleDerived X)} {n : ℤ} {M : X.Modules}
    (hComplex : IsDualizingComplex K H)
    (hCohomology : M = cohomologySheaf K n)
    (hCoherent : M.IsCoherent)
    (hVanishes : ∀ i : ℤ, i < n → IsZero (cohomologySheaf K i))
    (hNonzero : ¬ IsZero M) :
    IsDualizingModule K H n M := sorry

end IsDualizingModule

/-- A sheaf is a dualizing module in degree `n` exactly when it satisfies the five defining
dualizing-complex, cohomology, coherence, vanishing, and nonvanishing conditions. -/
theorem isDualizingModule_iff {X : RingedSpace.{u}} (K : ModuleDerived X)
    [MonoidalCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) (n : ℤ) (M : X.Modules) :
    IsDualizingModule K H n M ↔
      IsDualizingComplex K H ∧
        M = cohomologySheaf K n ∧ M.IsCoherent ∧
          (∀ i : ℤ, i < n → IsZero (cohomologySheaf K i)) ∧ ¬ IsZero M := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
