module

public import stacks_project.Chap71.Lemma_71_11_5_AffineRestriction
public import stacks_project.Chap71.Lemma_71_11_5_AffineTwists
public import stacks_project.Chap71.Lemma_71_11_5_BaseChange
public import stacks_project.Chap71.Lemma_71_11_5_Pointwise
public import stacks_project.Chap71.Lemma_71_11_5_TwistAlgebra
public import stacks_project.Chap71.Lemma_71_11_5_TwistBaseChangeLocal
public import stacks_project.Chap71.Lemma_71_11_5_TwistDescent
public import stacks_project.Chap71.Lemma_71_11_5_TwistModel
public import stacks_project.Chap71.Lemma_71_11_5_TwistPushforward

public import stacks_project.Chap71.Lemma_71_11_5_TwistBaseChange

/-!
# Lemma 71.11.5

Relative `Proj` of algebraic spaces commutes with base change: there is a canonical
isomorphism `r` with the fibre product over `X`, and a corresponding isomorphism `θ` of
`ℤ`-graded twist algebras.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open CategoryTheory.Limits
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.11.5 (1): for a scheme `S`, a morphism `g : X' ⟶ X` of algebraic spaces over `S`,
and a quasi-coherent graded `𝒪_X`-algebra `𝒜`, the canonical isomorphism
`r = canonicalBaseChangeIso : underline{Proj}_{X'}(g^* 𝒜) ≅ X' ×_X underline{Proj}_X(𝒜)`
of algebraic spaces is over `X'`. -/
@[stacks 085C]
theorem baseChangeIso_over {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X'))
    (deg' : DegreePieces 𝒜')
    (hAlg : AlgebraPullback g deg deg')
    (F' : ProjFunctor X' 𝒜') (hF' : F'.IsAssociatedToQuadruples deg') :
    (canonicalBaseChangeIso g hAlg hF hF').hom ≫ fibreProduct_fst g hF =
      toAlgebraicSpace_hom F' hF' :=
  sorry

/-- Lemma 71.11.5 (2): the corresponding isomorphism
`θ : r^* pr₂^*(⊕_{d : ℤ} 𝒪_P(d)) ⟶ ⊕_{d : ℤ} 𝒪_{P'}(d)` of `ℤ`-graded
`𝒪_{P'}`-algebras is `CanonicalTwists.BaseChange.data.theta`, the
`GradedAlgebraComparison` of `CanonicalTwists.family` along
`canonicalBaseChangeIso.hom ≫ fibreProduct_snd`, and each degree map is an
isomorphism. -/
@[stacks 085C]
theorem baseChange_theta_isIso {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X'))
    (deg' : DegreePieces 𝒜')
    (hAlg : AlgebraPullback g deg deg')
    (F' : ProjFunctor X' 𝒜') (hF' : F'.IsAssociatedToQuadruples deg') :
    ∀ n : ℤ, IsIso ((CanonicalTwists.BaseChange.data g hAlg hF hF').theta.degreeMap n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
