module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Cohomology.Comparison
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

/-- The degree-`q` underlying additive cohomology sheaf of every stage has vanishing positive
cohomology on every member of the basis. -/
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

/-- Basiswise acyclicity and vanishing of the section `R¹ lim` identify the degree-`q`
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

/-- Basiswise acyclicity of the underlying additive cohomology sheaves and vanishing of the
section `R¹ lim` identify the degree-`q` cohomology sheaf of a derived limit with the inverse
limit of the stage cohomology sheaves. -/
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
