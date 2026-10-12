/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap71.Lemma_71_11_9_Integral
public import stacks_project.Chap71.Lemma_71_11_10_FiniteType

/-!
# Lemma 71.11.9

In Situation 71.11.1, if `𝒪_X → 𝒜_0` is an integral algebra map and `𝒜` is of finite type as
an `𝒜_0`-algebra, then a morphism `π` that is étale-locally the scheme relative `Proj` of a
one-and-mul-preserving `Type u` section model of `𝒜`, via the canonical structure morphism
`etaleChartProj`, is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.11.9: in Situation 71.11.1, if `𝒪_X → 𝒜_0` is an integral algebra map and `𝒜` is
of finite type as an `𝒜_0`-algebra, then a morphism `π : P ⟶ X` that is étale-locally the
scheme relative `Proj` of a one-and-mul-preserving `Type u` section model of `𝒜`, via the
canonical structure morphism `etaleChartProj`, is universally closed. -/
@[stacks 084H]
theorem universallyClosed_of_integralDegreeZero
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π)
    (hIntegral : IntegralDegreeZeroAlgebra 𝒜)
    (hFiniteType : FiniteTypeAsDegreeZeroAlgebra 𝒜) :
    AlgebraicSpace.UniversallyClosed π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
