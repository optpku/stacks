module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Associated cycles of two-periodic homology

This file constructs the relative associated cycles of the homology sheaves of a coherent
two-periodic complex and records their rational equivalence under support-dimension bounds.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- Every homology sheaf of a two-periodic complex of coherent module sheaves is coherent. -/
theorem homology_isCoherent {X : Scheme.{u}} (K : TwoPeriodicEndomorphism X.Modules)
    [K.X.IsCoherent] (i : ZMod 2) : (K.toCochainComplex.homology i).IsCoherent := sorry

/-- The degree-`k` relative associated cycle of a homology sheaf of a coherent
two-periodic complex. -/
noncomputable def relativeHomologyCycle {S X : Scheme.{u}}
    (K : TwoPeriodicEndomorphism X.Modules) [K.X.IsCoherent]
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (i : ZMod 2) (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  Scheme.Modules.relativeAssociatedCycle
    (hF := homology_isCoherent K i) p δ (K.toCochainComplex.homology i) k

/-- The coefficients of a relative homology cycle are the associated-cycle coefficients
of the corresponding homology sheaf. -/
theorem relativeHomologyCycle_apply {S X : Scheme.{u}}
    (K : TwoPeriodicEndomorphism X.Modules) [K.X.IsCoherent]
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (i : ZMod 2) (k : ℤ) (x : X) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (K.relativeHomologyCycle p δ i k) x =
      @Scheme.Modules.associatedCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) (K.toCochainComplex.homology i)
        (homology_isCoherent K i) (p.relativeDimensionFunction δ) k x := sorry

/-- If the term of a coherent two-periodic complex has relative support dimension at most
`k + 1` and both homology sheaves have relative support dimension at most `k`, then their
degree-`k` relative associated cycles are rationally equivalent. -/
theorem homologyCycles_rationallyEquivalent
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (K : TwoPeriodicEndomorphism X.Modules) [K.X.IsCoherent] (k : ℤ)
    (hF : p.closedSubschemeDeltaDimension δ
      (schemeTheoreticSupport K.X) ≤ ((k + 1 : ℤ) : EInt))
    (hH0 : p.closedSubschemeDeltaDimension δ
      (schemeTheoreticSupport (K.toCochainComplex.homology 0)) ≤ (k : EInt))
    (hH1 : p.closedSubschemeDeltaDimension δ
      (schemeTheoreticSupport (K.toCochainComplex.homology 1)) ≤ (k : EInt)) :
    @RationalEquivalence.RationallyEquivalent X
      (LocallyOfFiniteType.isLocallyNoetherian p) (p.relativeDimensionFunction δ)
      inferInstance k (K.relativeHomologyCycle p δ 0 k)
      (K.relativeHomologyCycle p δ 1 k) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
