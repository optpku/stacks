/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.StageComparison
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local criteria for lower-truncation limits

This leaf owns the pointwise and basiswise vanishing conditions which make a compatible map to
the derived limit of the lower truncation tower invertible.  The conditions use module-valued open
cohomology, while `openCohomology_forget` supplies the source-facing additive-sheaf view.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.DerivedCategory.Truncation
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation

variable {X : RingedSpace.{u}}

/-- The iterated cohomology object `H^p(U, H^q(E))`, retaining its natural module structure over
`Γ(U, 𝒪_X)`. -/
@[stacks 0D62 "iterated open cohomology of a derived module"]
abbrev openCohomology (E : ModuleDerived X) (U : Opens X.carrier) (p : ℕ) (q : ℤ) :
  ModuleCat (sectionsRingOnOpen X U) :=
  AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.openCohomology E U p q

/-- Forgetting the section-ring action identifies `openCohomology E U p q` with the ordinary
cohomology of the underlying additive cohomology sheaf. -/
@[stacks 0D62 "underlying iterated open cohomology"]
theorem openCohomology_forget
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (E : ModuleDerived X) (U : Opens X.carrier) (p : ℕ) (q : ℤ) :
    (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
        (openCohomology E U p q) =
      ((moduleUnderlyingSheaf X).obj
        ((DerivedCategory.homologyFunctor X.Modules q).obj E)).H' p U := sorry

/-- Stacks 0D62: after shrinking any neighbourhood of each point, the objects
`H^p(U, H^(m-p)(E))` vanish above a point-dependent bound in every total degree `m`. -/
@[stacks 0D62 "pointwise eventual iterated-cohomology vanishing"]
def LocallyEventual (E : ModuleDerived X) : Prop :=
  ∀ x : X, ∃ bound : ℤ → ℤ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ m : ℤ, ∀ p : ℕ, bound m < (p : ℤ) →
            IsZero (openCohomology E U p (m - (p : ℤ)))

/-- The pointwise eventual condition supplies its bound and vanishing statement inside every
chosen neighbourhood. -/
@[stacks 0D62 "use of pointwise eventual vanishing"]
theorem LocallyEventual.existsShrink {E : ModuleDerived X} (hE : LocallyEventual E) (x : X) :
    ∃ bound : ℤ → ℤ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ m : ℤ, ∀ p : ℕ, bound m < (p : ℤ) →
              IsZero (openCohomology E U p (m - (p : ℤ))) := sorry

/-- Stacks 0D63: near each point there is one natural-number bound above which
`H^p(U, H^q(E))` vanishes simultaneously for every negative `q`. -/
@[stacks 0D63 "locally uniform negative-cohomology vanishing"]
def LocallyNegative (E : ModuleDerived X) : Prop :=
  ∀ x : X, ∃ d : ℕ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ q : ℤ, q < 0 → ∀ p : ℕ, d < p → IsZero (openCohomology E U p q)

/-- The locally uniform negative condition supplies a bound and a suitable shrinking of every
chosen neighbourhood. -/
@[stacks 0D63 "use of locally uniform negative vanishing"]
theorem LocallyNegative.existsShrink {E : ModuleDerived X} (hE : LocallyNegative E) (x : X) :
    ∃ d : ℕ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ q : ℤ, q < 0 → ∀ p : ℕ, d < p → IsZero (openCohomology E U p q) := sorry

/-- Locally uniform vanishing in every negative cohomological degree implies pointwise eventual
vanishing in each total degree. -/
@[stacks 0D63 "negative-to-eventual local vanishing bridge"]
theorem LocallyNegative.toLocallyEventual {E : ModuleDerived X} (hE : LocallyNegative E) :
    LocallyEventual E := sorry

namespace Basis

/-- A single degree-dependent bound for `H^p(U, H^(m-p)(E))` on every member of a basis. -/
@[stacks 08U2 "uniform eventual vanishing on an open basis"]
def Eventual (E : ModuleDerived X) (bound : ℤ → ℤ) (𝓑 : Set (Opens X.carrier)) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
    ∀ m : ℤ, ∀ p : ℕ, bound m < (p : ℤ) →
      IsZero (openCohomology E U p (m - (p : ℤ)))

/-- A single natural-number bound for `H^p(U, H^q(E))` on a basis, uniformly in every negative
cohomological degree `q`. -/
@[stacks 0D64 "uniform negative vanishing on an open basis"]
def Negative (E : ModuleDerived X) (d : ℕ) (𝓑 : Set (Opens X.carrier)) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
    ∀ p : ℕ, d < p → ∀ q : ℤ, q < 0 → IsZero (openCohomology E U p q)

/-- The source-facing additive-sheaf form of uniform negative cohomology vanishing on a basis. -/
@[stacks 071B "uniform negative vanishing for underlying cohomology sheaves"]
def SheafNegative (E : ModuleDerived X) (d : ℕ) (𝓑 : Set (Opens X.carrier))
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
    ∀ p : ℕ, d < p → ∀ q : ℤ, q < 0 →
      IsZero (((moduleUnderlyingSheaf X).obj
        ((DerivedCategory.homologyFunctor X.Modules q).obj E)).H' p U)

/-- The module-valued and underlying-sheaf forms of uniform negative vanishing agree. -/
@[stacks 071B "module and sheaf formulations of uniform negative vanishing"]
theorem negative_iff_sheafNegative
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (E : ModuleDerived X) (d : ℕ) (𝓑 : Set (Opens X.carrier)) :
    Negative E d 𝓑 ↔ SheafNegative E d 𝓑 := sorry

/-- Uniform eventual vanishing on a topological basis gives the pointwise shrinking condition. -/
@[stacks 08U2 "basiswise-to-local eventual vanishing"]
theorem Eventual.toLocal {E : ModuleDerived X} {bound : ℤ → ℤ}
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑) (hE : Eventual E bound 𝓑) :
    LocallyEventual E := sorry

/-- Uniform negative-degree vanishing on a topological basis gives the locally uniform shrinking
condition. -/
@[stacks 0D64 "basiswise-to-local negative vanishing"]
theorem Negative.toLocal {E : ModuleDerived X} {d : ℕ} {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑) (hE : Negative E d 𝓑) :
    LocallyNegative E := sorry

end Basis

namespace Comparison

/-- Stacks 0D62: a compatible lower-truncation comparison is invertible under pointwise eventual
iterated-cohomology vanishing. -/
@[stacks 0D62 "truncation comparison from pointwise eventual vanishing"]
theorem isIso_of_locallyEventual {E K : ModuleDerived X} {c : E ⟶ K}
    (hc : Lower.Comparison.Exists E c) (hE : LocallyEventual E) : IsIso c := sorry

/-- Stacks 0D63: a compatible lower-truncation comparison is invertible under locally uniform
vanishing for the negative cohomology objects. -/
@[stacks 0D63 "truncation comparison from locally uniform negative vanishing"]
theorem isIso_of_locallyNegative {E K : ModuleDerived X} {c : E ⟶ K}
    (hc : Lower.Comparison.Exists E c) (hE : LocallyNegative E) : IsIso c := sorry

/-- Stacks 08U2: a uniform eventual bound on an open basis makes a compatible lower-truncation
comparison invertible. -/
@[stacks 08U2 "truncation comparison from uniform basiswise eventual vanishing"]
theorem isIso_of_basisEventual {E K : ModuleDerived X} {c : E ⟶ K}
    (hc : Lower.Comparison.Exists E c) {bound : ℤ → ℤ} {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑) (hE : Basis.Eventual E bound 𝓑) : IsIso c := sorry

/-- Stacks 0D64: a uniform negative-degree bound on an open basis makes a compatible
lower-truncation comparison invertible. -/
@[stacks 0D64 "truncation comparison from uniform basiswise negative vanishing"]
theorem isIso_of_basisNegative {E K : ModuleDerived X} {c : E ⟶ K}
    (hc : Lower.Comparison.Exists E c) {d : ℕ} {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑) (hE : Basis.Negative E d 𝓑) : IsIso c := sorry

end Comparison

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation

end
