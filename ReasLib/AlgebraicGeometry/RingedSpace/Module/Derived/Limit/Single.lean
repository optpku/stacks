module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.BasisComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Limit
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Compatibility
public import ReasLib.Topology.Opens.Basis
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basiswise-acyclic limits of module sheaves

This file specializes the reusable ringed-site hypotheses for a sequential system of module
sheaves to the opens site of a ringed space.  The public surface retains `Opens.IsBasis`; proofs
can pass to the generic site formulation through the canonical `Opens.IsBasis.hasEnoughObjects`
bridge.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Single

variable {X : RingedSpace.{u}}

/-- Every stage of a module tower is acyclic on each member of the chosen open basis. -/
@[stacks 0BKS "basiswise acyclicity for a sequential system of modules"]
abbrev BasiswiseAcyclic (F : SequentialInverseSystem X.Modules)
    (𝓑 : Set (Opens X.carrier)) : Prop :=
  RingedSite.Hom.ModuleDerived.Limit.basiswiseAcyclic X.opensRingedSite 𝓑 F

/-- The first derived inverse limit of the stagewise section groups vanishes on each basis
open. -/
@[stacks 0BKS "basiswise first-derived-limit vanishing for module sections"]
abbrev BasiswiseR1Vanishing (F : SequentialInverseSystem X.Modules)
    (𝓑 : Set (Opens X.carrier)) : Prop :=
  RingedSite.Hom.ModuleDerived.Limit.basiswiseR1Vanishing X.opensRingedSite 𝓑 F

/-- The expanded open-hypercohomology form of `BasiswiseAcyclic`. -/
@[stacks 0BKS "expanded basiswise acyclicity for module towers"]
theorem basiswiseAcyclic_iff (F : SequentialInverseSystem X.Modules)
    (𝓑 : Set (Opens X.carrier)) :
    BasiswiseAcyclic F 𝓑 ↔
      ∀ U : Opens X.carrier, U ∈ 𝓑 → ∀ (n p : ℕ), 0 < p →
        IsZero (moduleOpenHypercohomology X U
          ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (F.obj (op n))) (p : ℤ)) := sorry

/-- The expanded section-functor form of `BasiswiseR1Vanishing`. -/
@[stacks 0BKS "expanded basiswise first-derived-limit vanishing"]
theorem basiswiseR1Vanishing_iff (F : SequentialInverseSystem X.Modules)
    (𝓑 : Set (Opens X.carrier)) :
    BasiswiseR1Vanishing F 𝓑 ↔
      ∀ U : Opens X.carrier, U ∈ 𝓑 →
        IsZero (SequentialInverseSystem.firstDerivedLimit
          (F ⋙ moduleSectionsAsAbelianFunctor X U)) := sorry

namespace Comparison

/-- Any derived limit of a basiswise-acyclic degree-zero tower is isomorphic to the degree-zero
object on its ordinary inverse limit. -/
@[stacks 0BKS "basiswise-acyclic derived limit comparison"]
theorem isoLimit (F : SequentialInverseSystem X.Modules) (K : ModuleDerived X)
    (hK : IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ)) K)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hacyclic : BasiswiseAcyclic F 𝓑)
    (hR1lim : BasiswiseR1Vanishing F 𝓑) :
    IsIsomorphic K
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) := sorry

end Comparison

/-- The degree-zero object on the ordinary limit is a homotopy limit of the degree-zero tower.
This Prop-valued formulation is the canonical statement that no presentation data need be
chosen. -/
@[stacks 0BKS "ordinary limit is the homotopy limit of a basiswise-acyclic tower"]
theorem isOf (F : SequentialInverseSystem X.Modules)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hacyclic : BasiswiseAcyclic F 𝓑)
    (hR1lim : BasiswiseR1Vanishing F 𝓑) :
    HomotopyLimit.IsOf
      (F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ))
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) := sorry

/-- The ordinary inverse limit, placed in degree zero, is a derived limit of a
basiswise-acyclic module tower.  The result is `Nonempty` because a derived-limit presentation
is auxiliary data rather than a canonical output.  New consumers should normally use `isOf`. -/
@[stacks 0BKS "ordinary limit computes a basiswise-acyclic derived limit"]
theorem existsDerivedLimit (F : SequentialInverseSystem X.Modules)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hacyclic : BasiswiseAcyclic F 𝓑)
    (hR1lim : BasiswiseR1Vanishing F 𝓑) :
    Nonempty (IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ))
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F))) := sorry

/-- Under the same basiswise hypotheses, the ordinary inverse limit has zero positive
cohomology on every basis open. -/
@[stacks 0BKS "higher cohomology of a basiswise-acyclic inverse limit"]
theorem higherCohomologyIsZero (F : SequentialInverseSystem X.Modules)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hacyclic : BasiswiseAcyclic F 𝓑)
    (hR1lim : BasiswiseR1Vanishing F 𝓑)
    {U : Opens X.carrier} (hU : U ∈ 𝓑) (p : ℕ) (hp : 0 < p) :
    IsZero (moduleOpenHypercohomology X U
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) (p : ℤ)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Single

end
