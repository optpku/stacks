/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_5_3_Coproducts

/-!
# Classical generators of compact quasicoherent complexes on algebraic spaces

A perfect weak generator of `D_QCoh(𝒪_X)` on a quasi-compact and quasi-separated
algebraic space classically generates the compact objects, equivalently the
perfect objects.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A perfect weak generator of the derived category of modules with quasi-coherent
cohomology on a quasi-compact and quasi-separated algebraic space classically generates
its compact objects. -/
theorem isClassicalGeneratorOfCompacts {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (G : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj)
    (hG_generator : IsWeakGenerator G) :
    IsClassicalGeneratorOfCompacts G := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
