/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.ComplexComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of sequential limits of module complexes

This file specializes the ringed-site complex-tower API to the opens of a ringed space.  Its
covering hypothesis is `Opens.IsBasis` itself: an arbitrary topological basis need not be downward
closed, so it is not repackaged as `HasEnoughObjectsWithProperty (· ∈ 𝓑)`.
-/

@[expose] public section

-- Local instance justification (proof-local temporary data): the degreewise and cohomology tower comparisons commute limits through the fixed moduleUnderlyingSheaf functor using its named preservation proof.
attribute [local instance] AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesLimitsOfShape


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Complex

variable {X : RingedSpace.{u}}

/-- The degree-`m` homology functor on cochain complexes of `𝒪_X`-modules. -/
@[stacks 08BY "homology functor for module complexes"]
abbrev homologyFunctor (X : RingedSpace.{u}) (m : ℤ) :
    CochainComplex X.Modules ℤ ⥤ X.Modules :=
  HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) m

/-- The tower of degree-`m` homology modules associated to a tower of cochain complexes. -/
@[stacks 08BY "homology tower of module complexes"]
abbrev homologyTower (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ) :
    SequentialInverseSystem X.Modules :=
  F ⋙ homologyFunctor X m

namespace Degree

/-- The tower `n ↦ F_n^i(U)` of degree-`i` sections over an open `U`. -/
@[stacks 08BY "degreewise section tower"]
abbrev tower (F : SequentialInverseSystem (CochainComplex X.Modules ℤ))
    (U : Opens X.carrier) (i : ℤ) : SequentialInverseSystem AddCommGrpCat.{u} :=
  RingedSite.Hom.ModuleSections.Underlying.complexDegreeTower (opensRingedSite X) F U i

/-- The degree-`i` section towers have vanishing `R¹ lim` on every member of `𝓑`. -/
@[stacks 08BY "basiswise degree-tower R1-limit vanishing"]
def R1Vanishing (F : SequentialInverseSystem (CochainComplex X.Modules ℤ))
    (𝓑 : Set (Opens X.carrier)) (i : ℤ) : Prop :=
  ∀ U : Opens X.carrier, U ∈ 𝓑 → IsZero (tower F U i).firstDerivedLimit

/-- Basiswise degree-tower vanishing specializes to one basis open. -/
@[stacks 08BY "specialization of degree-tower R1-limit vanishing"]
theorem R1Vanishing.at {F : SequentialInverseSystem (CochainComplex X.Modules ℤ)}
    {𝓑 : Set (Opens X.carrier)} {i : ℤ} (hF : R1Vanishing F 𝓑 i)
    {U : Opens X.carrier} (hU : U ∈ 𝓑) : IsZero (tower F U i).firstDerivedLimit := sorry

end Degree

namespace Cohomology

/-- The tower `n ↦ H^i(F_n(U))` of section cohomology over an open `U`. -/
@[stacks 08BY "cohomology section tower"]
abbrev tower (F : SequentialInverseSystem (CochainComplex X.Modules ℤ))
    (U : Opens X.carrier) (i : ℤ) : SequentialInverseSystem AddCommGrpCat.{u} :=
  RingedSite.Hom.ModuleSections.Underlying.complexCohomologyTower (opensRingedSite X) F U i

/-- The degree-`i` cohomology section towers have vanishing `R¹ lim` on every member of `𝓑`. -/
@[stacks 08BY "basiswise cohomology-tower R1-limit vanishing"]
def R1Vanishing (F : SequentialInverseSystem (CochainComplex X.Modules ℤ))
    (𝓑 : Set (Opens X.carrier)) (i : ℤ) : Prop :=
  ∀ U : Opens X.carrier, U ∈ 𝓑 → IsZero (tower F U i).firstDerivedLimit

/-- On every member of `𝓑`, the degree-`i` cohomology tower is constant after stage `n₀`. -/
@[stacks 08BY "basiswise eventual constancy of cohomology towers"]
def EventuallyConstant (F : SequentialInverseSystem (CochainComplex X.Modules ℤ))
    (𝓑 : Set (Opens X.carrier)) (i : ℤ) (n₀ : ℕ) : Prop :=
  ∀ U : Opens X.carrier, U ∈ 𝓑 → ∀ n : ℕ, ∀ hn : n₀ ≤ n,
    IsIso ((tower F U i).transitionMap hn)

/-- Basiswise cohomology-tower vanishing specializes to one basis open. -/
@[stacks 08BY "specialization of cohomology-tower R1-limit vanishing"]
theorem R1Vanishing.at {F : SequentialInverseSystem (CochainComplex X.Modules ℤ)}
    {𝓑 : Set (Opens X.carrier)} {i : ℤ} (hF : R1Vanishing F 𝓑 i)
    {U : Opens X.carrier} (hU : U ∈ 𝓑) : IsZero (tower F U i).firstDerivedLimit := sorry

/-- Basiswise eventual constancy specializes to a transition map over one basis open. -/
@[stacks 08BY "specialization of basiswise eventual constancy"]
theorem EventuallyConstant.transitionMap {F : SequentialInverseSystem (CochainComplex X.Modules ℤ)}
    {𝓑 : Set (Opens X.carrier)} {i : ℤ} {n₀ : ℕ}
    (hF : EventuallyConstant F 𝓑 i n₀) {U : Opens X.carrier} (hU : U ∈ 𝓑)
    (n : ℕ) (hn : n₀ ≤ n) : IsIso ((tower F U i).transitionMap hn) := sorry

end Cohomology

/-- The canonical comparison `H^m(lim F) ⟶ lim H^m(F)`. -/
@[stacks 08BY "cohomology comparison for a complex tower"]
abbrev comparison (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ) :=
  limit.post F (homologyFunctor X m)

/-- The canonical projection `lim H^m(F) ⟶ H^m(F_{n₀})`. -/
@[stacks 08BY "cohomology-tower stage projection"]
abbrev projection (F : SequentialInverseSystem (CochainComplex X.Modules ℤ))
    (m : ℤ) (n₀ : ℕ) :=
  limit.π (homologyTower F m) (op n₀)

namespace Underlying

/-- After forgetting module structure, `comparison` is the additive-sheaf comparison transported
across the canonical limit-preservation isomorphism. -/
@[stacks 08BY "underlying additive-sheaf comparison map"]
theorem comparison_comp_preservesLimitIso
    (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ) :
    (moduleUnderlyingSheaf X).map (comparison F m) ≫
        (preservesLimitIso (moduleUnderlyingSheaf X) (homologyTower F m)).hom =
      limit.post F (homologyFunctor X m ⋙ moduleUnderlyingSheaf X) := sorry

/-- The preservation isomorphism transports an additive-sheaf stage projection to the image of
the corresponding module-valued projection. -/
@[stacks 08BY "underlying additive-sheaf stage projection"]
theorem preservesLimitIso_hom_comp_π
    (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ) (j : ℕᵒᵖ) :
    (preservesLimitIso (moduleUnderlyingSheaf X) (homologyTower F m)).hom ≫
        limit.π (homologyTower F m ⋙ moduleUnderlyingSheaf X) j =
      (moduleUnderlyingSheaf X).map (limit.π (homologyTower F m) j) := sorry

end Underlying

namespace Comparison

/-- Basiswise `R¹ lim` vanishing in the two relevant complex degrees and the preceding
cohomological degree makes the cohomology comparison invertible. -/
@[stacks 08BY "basiswise cohomology comparison isomorphism"]
theorem isIso (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hdegree₂ : Degree.R1Vanishing F 𝓑 (m - 2))
    (hdegree₁ : Degree.R1Vanishing F 𝓑 (m - 1))
    (hcohom₁ : Cohomology.R1Vanishing F 𝓑 (m - 1)) : IsIso (comparison F m) := sorry

end Comparison

namespace Projection

/-- Basiswise eventual constancy of degree-`m` cohomology makes the stage projection invertible. -/
@[stacks 08BY "basiswise cohomology projection isomorphism"]
theorem isIso (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ) (n₀ : ℕ)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hconstant : Cohomology.EventuallyConstant F 𝓑 m n₀) : IsIso (projection F m n₀) := sorry

end Projection

namespace Comparison

/-- Under the comparison and eventual-constancy hypotheses, the canonical map from the
cohomology of the limit complex to stage `n₀` is invertible. -/
@[stacks 08BY "cohomology of a complex limit at an eventual stage"]
theorem compProjection_isIso
    (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ) (n₀ : ℕ)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hdegree₂ : Degree.R1Vanishing F 𝓑 (m - 2))
    (hdegree₁ : Degree.R1Vanishing F 𝓑 (m - 1))
    (hcohom₁ : Cohomology.R1Vanishing F 𝓑 (m - 1))
    (hconstant : Cohomology.EventuallyConstant F 𝓑 m n₀) :
    IsIso (comparison F m ≫ projection F m n₀) := sorry

/-- Stacks 08BY: the cohomology comparison and the eventual stage projection are both
isomorphisms under the corresponding basiswise hypotheses. -/
@[stacks 08BY "comparison and eventual projection for a complex limit"]
theorem andProjection_isIso
    (F : SequentialInverseSystem (CochainComplex X.Modules ℤ)) (m : ℤ) (n₀ : ℕ)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑)
    (hdegree₂ : Degree.R1Vanishing F 𝓑 (m - 2))
    (hdegree₁ : Degree.R1Vanishing F 𝓑 (m - 1))
    (hcohom₁ : Cohomology.R1Vanishing F 𝓑 (m - 1))
    (hconstant : Cohomology.EventuallyConstant F 𝓑 m n₀) :
    IsIso (comparison F m) ∧ IsIso (projection F m n₀) := sorry

end Comparison

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Complex

end
