module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Presheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basiswise acyclic cohomology sheaves on a ringed space

The core predicates retain the natural module structure on open cohomology.  Separate
`SheafAcyclicIn` and `SheafAcyclic` views record the textbook formulation through `Sheaf.H'`;
only the comparison API between the two views needs an explicit `HasExt` instance.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.Basis

variable {X : RingedSpace.{u}}

/-- The degree-`q` cohomology module of `K` is acyclic on every member of the open basis `𝓑`. -/
@[stacks 0BKT "basiswise acyclicity in one cohomological degree"]
def AcyclicIn (K : ModuleDerived X) (𝓑 : Set (Opens X.carrier)) (q : ℤ) : Prop :=
  ∀ U : Opens X.carrier, U ∈ 𝓑 → ∀ p : ℕ, 0 < p →
    IsZero (openCohomology K U p q)

/-- Every cohomology module of `K` is acyclic on every member of the open basis `𝓑`. -/
@[stacks 0BKT "basiswise acyclic cohomology modules"]
def Acyclic (K : ModuleDerived X) (𝓑 : Set (Opens X.carrier)) : Prop :=
  ∀ q : ℤ, AcyclicIn K 𝓑 q

/-- The source-facing formulation of degree-`q` basiswise acyclicity through the ordinary
cohomology of the underlying additive cohomology sheaf. -/
@[stacks 0BKT "basiswise acyclicity of one underlying cohomology sheaf"]
def SheafAcyclicIn (K : ModuleDerived X) (𝓑 : Set (Opens X.carrier)) (q : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] : Prop :=
  ∀ U : Opens X.carrier, U ∈ 𝓑 → ∀ p : ℕ, 0 < p →
    IsZero ((sheaf X K q).H' p U)

/-- Every underlying additive cohomology sheaf of `K` is acyclic on the basis `𝓑`. -/
@[stacks 0BKT "basiswise acyclic underlying cohomology sheaves"]
def SheafAcyclic (K : ModuleDerived X) (𝓑 : Set (Opens X.carrier))
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] : Prop :=
  ∀ q : ℤ, SheafAcyclicIn K 𝓑 q

/-- Basiswise acyclicity in all degrees specializes to one cohomological degree. -/
@[stacks 0BKT "degree specialization of basiswise acyclicity"]
theorem Acyclic.inDegree {K : ModuleDerived X} {𝓑 : Set (Opens X.carrier)}
    (hK : Acyclic K 𝓑) (q : ℤ) : AcyclicIn K 𝓑 q := sorry

/-- Sheafwise basis acyclicity in all degrees specializes to one cohomological degree. -/
@[stacks 0BKT "degree specialization of sheafwise basis acyclicity"]
theorem SheafAcyclic.inDegree
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {K : ModuleDerived X} {𝓑 : Set (Opens X.carrier)}
    (hK : SheafAcyclic K 𝓑) (q : ℤ) : SheafAcyclicIn K 𝓑 q := sorry

/-- The module-valued and underlying-sheaf formulations in a fixed degree agree whenever the
additive derived category supplies `HasExt`. -/
@[stacks 0BKT "module and sheaf acyclicity in one degree"]
theorem acyclicIn_iff_sheafAcyclicIn
    (K : ModuleDerived X) (𝓑 : Set (Opens X.carrier)) (q : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] :
    AcyclicIn K 𝓑 q ↔ SheafAcyclicIn K 𝓑 q := sorry

/-- The module-valued and underlying-sheaf formulations in every degree agree whenever the
additive derived category supplies `HasExt`. -/
@[stacks 0BKT "module and sheaf formulations of basiswise acyclicity"]
theorem acyclic_iff_sheafAcyclic (K : ModuleDerived X) (𝓑 : Set (Opens X.carrier))
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] :
    Acyclic K 𝓑 ↔ SheafAcyclic K 𝓑 := sorry

/-- Stacks 0BKT: on a member of a basis where the degree-`q` cohomology module of `K` is
acyclic, hypercohomology is its degree-zero open cohomology. -/
@[stacks 0BKT "hypercohomology from basiswise acyclicity in one degree"]
theorem zeroDegreeIso (K : ModuleDerived X) {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑) (q : ℤ) (hK : AcyclicIn K 𝓑 q)
    {U : Opens X.carrier} (hU : U ∈ 𝓑) :
    IsIsomorphic (moduleOpenHypercohomology X U K q)
      ((forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
        (openCohomology K U 0 q)) := sorry

/-- Source-facing fixed-degree companion of `zeroDegreeIso`, expressed as ordinary degree-zero
cohomology of the underlying additive cohomology sheaf. -/
@[stacks 0BKT "hypercohomology from one acyclic underlying cohomology sheaf"]
theorem zeroDegreeIsoOfSheaf (K : ModuleDerived X) {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑) (q : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (hK : SheafAcyclicIn K 𝓑 q) {U : Opens X.carrier} (hU : U ∈ 𝓑) :
    IsIsomorphic (moduleOpenHypercohomology X U K q) ((sheaf X K q).H' 0 U) := sorry

/-- Source-facing all-degrees companion of `zeroDegreeIso`, matching the textbook hypothesis
that every cohomology sheaf of `K` is acyclic on `𝓑`. -/
@[stacks 0BKT "hypercohomology from acyclic underlying cohomology sheaves"]
theorem zeroDegreeIsoOfSheaves (K : ModuleDerived X) {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑)
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (hK : SheafAcyclic K 𝓑) {U : Opens X.carrier} (hU : U ∈ 𝓑) (q : ℤ) :
    IsIsomorphic (moduleOpenHypercohomology X U K q) ((sheaf X K q).H' 0 U) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.Basis

end
