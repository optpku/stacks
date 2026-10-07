module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberBetti
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.FlatCoefficients
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ResidueField

/-!
# Dimensions of cohomology on fibers

This file defines the fiberwise cohomology finrank of a scheme module and records its
comparison with the fiber Betti function of the derived pushforward.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree-`i` dimension of the cohomology of the fiber of `ℱ` over a point of the
base, with negative-degree values defined to be zero. -/
noncomputable def fiberCohomologyFinrank {X S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) (i : ℤ) : S → ℕ :=
  fun s ↦ if 0 ≤ i then
    cohomologyFinrank (f.fiberToSpecResidueField s)
      ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ) i.toNat
  else 0

/-- The fiber cohomology finrank is computed by ordinary cohomology in nonnegative
degrees and is zero in negative degrees. -/
theorem fiberCohomologyFinrank_apply {X S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) (i : ℤ) (s : S) :
    fiberCohomologyFinrank f ℱ i s = if 0 ≤ i then
      cohomologyFinrank (f.fiberToSpecResidueField s)
        ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ) i.toNat
    else 0 := sorry

/-- The fiber-cohomology finrank agrees with the fiber Betti function of the derived
pushforward of `ℱ` placed in degree zero. -/
theorem fiberCohomologyFinrank_eq_pushforwardFiberBetti
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
    (i : ℤ) :
    fiberCohomologyFinrank f ℱ i =
      Scheme.ModuleDerived.fiberBetti
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) i := sorry

/-- Formation of the fiber-cohomology finrank function commutes with arbitrary
cartesian base change. -/
theorem fiberCohomologyFinrank_baseChange
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
    (sq : IsPullback g' f' f g) (i : ℤ) :
    fiberCohomologyFinrank f' ((Scheme.Modules.pullback g').obj ℱ) i =
      fun s' : S' ↦ fiberCohomologyFinrank f ℱ i (g s') := sorry

/-- Every fiber-cohomology finrank function is upper semicontinuous. -/
theorem fiberCohomologyFinrank_upperSemicontinuous
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
    (i : ℤ) :
    UpperSemicontinuous (fiberCohomologyFinrank f ℱ i) := sorry

/-- Every level set of a fiber-cohomology finrank function is locally constructible. -/
theorem fiberCohomologyFinrank_levelSet_isLocallyConstructible
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
    (i : ℤ) (n : ℕ) :
    Topology.IsLocallyConstructible ((fiberCohomologyFinrank f ℱ i) ⁻¹' {n}) := sorry

end AlgebraicGeometry.Scheme.Hom
