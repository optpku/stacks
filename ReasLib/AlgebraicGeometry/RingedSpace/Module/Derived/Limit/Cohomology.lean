/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Limit
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology sheaves of basiswise-acyclic derived limits

The two tower abbreviations below are the canonical sheaf-valued and section-valued views of a
sequential system.  The comparison theorem keeps the basiswise acyclicity and `R¹ lim` hypotheses
separate, so either condition can be reused by another limit argument.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

variable {X : RingedSpace.{u}}

/-- The tower of underlying additive cohomology sheaves of a sequential system of derived modules. -/
@[stacks 0BKU "cohomology-sheaf tower of a derived inverse system"]
abbrev cohomologySheafTower (Ksys : SequentialInverseSystem (ModuleDerived X)) (q : ℤ) :
    SequentialInverseSystem (X.carrier.Sheaf AddCommGrpCat.{u}) :=
  Ksys ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙ moduleUnderlyingSheaf X

/-- The tower of degree-`q` section groups over a fixed open. -/
@[stacks 0BKU "open section cohomology tower"]
abbrev sectionCohomologyTower (Ksys : SequentialInverseSystem (ModuleDerived X))
    (U : Opens X.carrier) (q : ℤ) : SequentialInverseSystem AddCommGrpCat.{u} :=
  Ksys ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙
    moduleSectionsAsAbelianFunctor X U

/-- Basiswise vanishing of the positive open cohomology of every stage of a sequential system. -/
@[stacks 0BKU "basiswise positive-cohomology vanishing"]
def BasiswiseAcyclic (Ksys : SequentialInverseSystem (ModuleDerived X))
    (𝓑 : Set (Opens X.carrier)) (q : ℤ) : Prop :=
  ∀ n : ℕ, Basis.AcyclicIn (Ksys.obj (op n)) 𝓑 q

/-- The source-facing additive-sheaf formulation of basiswise acyclicity.  It is kept as a
bridge because `Sheaf.H'` needs an explicit `HasExt` instance, while the module-valued condition
is the canonical core predicate. -/
@[stacks 0BKU "basiswise acyclicity in the underlying sheaf view"]
def SheafwiseAcyclic (Ksys : SequentialInverseSystem (ModuleDerived X))
    (𝓑 : Set (Opens X.carrier)) (q : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] : Prop :=
  ∀ n : ℕ, Basis.SheafAcyclicIn (Ksys.obj (op n)) 𝓑 q

/-- The module-valued and underlying-sheaf formulations of basiswise acyclicity agree whenever
the additive derived category supplies `HasExt`. -/
@[stacks 0BKU "module and sheaf formulations of basiswise acyclicity"]
theorem basiswiseAcyclic_iff_sheafwiseAcyclic
    (Ksys : SequentialInverseSystem (ModuleDerived X)) (𝓑 : Set (Opens X.carrier)) (q : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] :
    BasiswiseAcyclic Ksys 𝓑 q ↔ SheafwiseAcyclic Ksys 𝓑 q := sorry

namespace Comparison

/-- Stacks 0BKU: basiswise acyclicity and vanishing of the section `R¹ lim` identify the degree-`q`
cohomology sheaf of a sequential derived limit with the inverse limit of the stage cohomology
sheaves. -/
@[stacks 0BKU "basiswise derived-limit cohomology comparison"]
theorem isoLimit
    (Ksys : SequentialInverseSystem (ModuleDerived X)) (K : ModuleDerived X)
    (hK : IsDerivedLimit Ksys K) {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑) (q : ℤ)
    (hacyclic : BasiswiseAcyclic Ksys 𝓑 q)
    (hR1lim :
      ∀ U : Opens X.carrier, U ∈ 𝓑 →
        IsZero (sectionCohomologyTower Ksys U q).firstDerivedLimit) :
    IsIsomorphic (Cohomology.sheaf X K q)
      (limit (cohomologySheafTower Ksys q)) := sorry

/-- Source-facing companion of the basiswise derived-limit comparison, using the ordinary
cohomology groups of the underlying additive cohomology sheaves. -/
@[stacks 0BKU "underlying-sheaf basiswise derived-limit comparison"]
theorem isoLimitOfSheaves
    (Ksys : SequentialInverseSystem (ModuleDerived X)) (K : ModuleDerived X)
    (hK : IsDerivedLimit Ksys K) {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑) (q : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (hacyclic : SheafwiseAcyclic Ksys 𝓑 q)
    (hR1lim :
      ∀ U : Opens X.carrier, U ∈ 𝓑 →
        IsZero (sectionCohomologyTower Ksys U q).firstDerivedLimit) :
    IsIsomorphic (Cohomology.sheaf X K q)
      (limit (cohomologySheafTower Ksys q)) := sorry

end Comparison

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

end
