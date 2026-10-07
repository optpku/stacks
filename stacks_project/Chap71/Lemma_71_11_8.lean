module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_11_10_FiniteType

/-!
# Lemma 71.11.8

In Situation 71.11.1, if `𝒜` is of finite type as a sheaf of `𝒪_X`-algebras, then a morphism
`π` that is étale-locally the scheme relative `Proj` of a one-and-mul-preserving `Type u`
section model of `𝒜`, via the canonical structure morphism `etaleChartProj`, is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.11.8: in Situation 71.11.1, if `𝒜` is of finite type as a sheaf of `𝒪_X`-algebras,
then a morphism `π : P ⟶ X` that is étale-locally the scheme relative `Proj` of a
one-and-mul-preserving `Type u` section model of `𝒜`, via the canonical structure morphism
`etaleChartProj`, is of finite type. -/
@[stacks 084G]
theorem finiteType_of_finiteTypeAsBase
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π)
    (h𝒜 : FiniteTypeAsBaseAlgebra 𝒜) : AlgebraicSpace.FiniteType π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
