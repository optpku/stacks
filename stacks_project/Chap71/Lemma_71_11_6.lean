module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap71.Lemma_71_11_10_FiniteType

/-!
# Lemma 71.11.6

In Situation 71.11.1, a morphism `π` that is étale-locally the scheme relative `Proj` of a
one-and-mul-preserving `Type u` section model of `𝒜` is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.11.6: in Situation 71.11.1, a morphism `π : P ⟶ X` that is étale-locally the scheme
relative `Proj` of a one-and-mul-preserving `Type u` section model of `𝒜`, via the canonical
structure morphism `etaleChartProj`, is separated. -/
@[stacks 084E]
theorem separated
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π) : Separated π := sorry

/-- Every affine-étale base change of a morphism that is étale-locally the scheme relative `Proj`
of a one-and-mul-preserving `Type u` section model of `𝒜` is separated. -/
theorem separated_etaleBaseChange
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π) (U : affineEtaleSite X) :
    Separated (etaleBaseChangeSnd π U.obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
