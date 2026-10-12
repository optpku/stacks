/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_4_Psi
public import stacks_project.Chap71.Lemma_71_11_4_BaseChange

/-!
# Lemma 71.11.4

In Situation 71.11.1, the relative Proj carries a quasi-coherent sheaf of
ℤ-graded algebras ⊕_{n : ℤ} 𝒪_P(n) and a canonical homomorphism
ψ : π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_P(n) whose base change to any scheme over X agrees
with Constructions Lemma 27.15.5.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.11.4 (1): the sheaf of ℤ-graded algebras
⊕_{n : ℤ} 𝒪_{underline{Proj}_X(𝒜)}(n) is quasi-coherent. -/
@[stacks 084D]
theorem algebra_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) :
    (CanonicalTwists.algebra F hF).IsQuasicoherent :=
  sorry

/-- Lemma 71.11.4 (2): there is a canonical homomorphism of graded algebras
ψ : π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_{underline{Proj}_X(𝒜)}(n), preserving the unit and
homogeneous multiplication. -/
@[stacks 084D]
theorem psi_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) :
    CanonicalTwists.CanonicalHom.spec (CanonicalTwists.psi F hF) :=
  sorry

/-- Lemma 71.11.4 (3): for any scheme morphism `g : Z ⟶ X` and any affine open
`U ⊂ Z`, after source transport and the canonical target identification
`affineChartTwistIso` of the restricted pullback of `𝒪_P(n)` with the
affine-model twisting sheaf, the restriction of the pullback of `ψ` to a
positive-degree chart of `underline{Proj}_U(g^* 𝒜|_U)` equals the
Constructions Lemma 27.15.5 affine chart map `homogeneousPullbackMap` of
`g^* 𝒜|_U`, pulled back along the classifying section of that chart. -/
@[stacks 084D]
theorem psi_baseChange {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} [𝒜.IsCommutative] (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) {Z : Over S} (g : ofOver Z ⟶ X)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (CanonicalTwists.affineOpenOver U).left
      (CanonicalTwists.affineOpenAlgebra g deg U)]
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    CanonicalTwists.affineChartPsiComparison g F hF U d n =
      CanonicalTwists.affineChartPsiModel g F hF U d n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
