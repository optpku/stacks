/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap71.Lemma_71_11_10_FiniteType

/-!
# Lemma 71.11.10

In Situation 71.11.1, finite type of `𝒜_0` as an `𝒪_X`-module together with finite type of
`𝒜` as an `𝒜_0`-algebra is equivalent to the same module-finiteness together with finite type
of `𝒜` as an `𝒪_X`-algebra. If these hold, then a morphism `π` that is étale-locally the scheme
relative `Proj` of a one-and-mul-preserving `Type u` section model of `𝒜`, via the canonical
structure morphism `etaleChartProj`, is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.11.10 (1): in Situation 71.11.1, `(deg.obj 0).IsFiniteType` together with
`FiniteTypeAsDegreeZeroAlgebra 𝒜` is equivalent to `(deg.obj 0).IsFiniteType` together with
`FiniteTypeAsBaseAlgebra 𝒜`. -/
@[stacks 084I]
theorem finiteTypeConditions_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) :
    ((deg.obj 0).IsFiniteType ∧ FiniteTypeAsDegreeZeroAlgebra 𝒜) ↔
      ((deg.obj 0).IsFiniteType ∧ FiniteTypeAsBaseAlgebra 𝒜) := sorry

/-- Lemma 71.11.10 (2): if `(deg.obj 0).IsFiniteType` and `FiniteTypeAsDegreeZeroAlgebra 𝒜`
hold, then a morphism `π : P ⟶ X` that is étale-locally the scheme relative `Proj` of a
one-and-mul-preserving `Type u` section model of `𝒜`, via the canonical structure morphism
`etaleChartProj`, is proper. -/
@[stacks 084I]
theorem proper_of_finiteType
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π) :
    (deg.obj 0).IsFiniteType ∧ FiniteTypeAsDegreeZeroAlgebra 𝒜 → Proper π := sorry

/-- If `(deg.obj 0).IsFiniteType` and `FiniteTypeAsBaseAlgebra 𝒜` hold, then a morphism `π`
that is étale-locally the scheme relative `Proj` of a one-and-mul-preserving `Type u` section
model of `𝒜`, via the canonical structure morphism `etaleChartProj`, is proper. -/
theorem proper_of_finiteTypeAsBase
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π) :
    (deg.obj 0).IsFiniteType ∧ FiniteTypeAsBaseAlgebra 𝒜 → Proper π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
