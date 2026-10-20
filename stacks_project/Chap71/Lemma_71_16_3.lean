module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap70.Lemma_70_9_2_Generation
public import stacks_project.Chap71.Lemma_71_16_2_DegreeSubobject

/-!
# Lemma 71.16.3

A finitely presented closed subspace of a quasi-compact relative Proj of a
quasi-coherent graded algebra on a quasi-compact quasi-separated algebraic
space, missing a quasi-compact open of the base, is itself relative Proj of
the quotient by a finite-type quasi-coherent submodule in one positive degree
whose degree quotient is supported away from that open.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.16.3
Let `S` be a scheme and let `X` be a quasi-compact quasi-separated algebraic
space over `S`. Let `𝒜` be a quasi-coherent graded `𝒪_X`-algebra, and let
`π : P = underline{Proj}_X(𝒜) ⟶ X` be the relative Proj of `𝒜`. Let
`i : Z ⟶ P` be a closed subspace, and let `U ⊂ X` be an open. If `π` is
quasi-compact, `i` is of finite presentation, `|U| ∩ |π|(|i|(|Z|)) = ∅`,
`U` is quasi-compact, and `𝒜_n` is a finite type `𝒪_X`-module for all `n`,
then there exist `d > 0` and a quasi-coherent finite type `𝒪_X`-submodule
`G ⊂ 𝒜_d` such that `Z = underline{Proj}_X(𝒜 / G 𝒜)` and the support of
`𝒜_d / G` is disjoint from `U`. -/
@[stacks 085N]
theorem existsQuotientByFiniteTypeDegreeSubobject_support_disjoint
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] [𝒜.IsQuasicoherent]
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) {Z : AlgebraicSpace S}
    (i : Z ⟶ toAlgebraicSpace F hF)
    [IsClosedImmersion i] [QuasiCompact (toAlgebraicSpace_hom F hF)]
    [FinitePresentation i] (hfinite : ∀ n : ℕ, (deg.obj n).IsFiniteType)
    (U : OpenSubspace X) [IsQuasiCompact U.X]
    (hdisjoint :
      Disjoint U.pointsSet
        (Set.range (Points.map (i ≫ toAlgebraicSpace_hom F hF)))) :
    ∃ (d : ℕ) (G : Subobject (deg.obj d))
      (Q : ClosedSubspaceQuotient F hF i),
      0 < d ∧ G ∈ finiteTypeQuasiCoherentSubobjects (deg.obj d) ∧
        Q.IsQuotientByDegreeSubobject d G ∧
          Disjoint (moduleSupport (cokernel G.arrow)) U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
