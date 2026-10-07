module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap81.Lemma_81_10_10_SupportedOn

/-!
# Classical generators of compact supported quasicoherent complexes

A perfect weak generator of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated
algebraic space, for a closed subset `T` with quasi-compact complement, classically
generates the compact objects, equivalently the perfect objects.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- The property of having quasi-coherent cohomology supported on a subset is
triangulated. -/
instance quasiCoherentSupportedOn_isTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Points X)) :
    (quasiCoherentSupportedOn X T).IsTriangulated := sorry

/-- The derived category of quasi-coherent modules supported on a subset admits
coproducts indexed by types in the ambient universe. -/
instance hasCoproducts {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Set (Points X)) :
    HasCoproducts.{u} (SupportedOn X T) := sorry

/-- A perfect weak generator of the derived category of quasi-coherent modules supported
on a closed subset with quasi-compact complement, on a quasi-compact and quasi-separated
algebraic space, classically generates its compact objects. -/
theorem isClassicalGeneratorOfCompacts {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl))
    (G : SupportedOn X (T : Set (Points X)))
    (hG_perfect : ModuleDerived.IsPerfect G.obj)
    (hG_generator : IsWeakGenerator G) :
    IsClassicalGeneratorOfCompacts G := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
