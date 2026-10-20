module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Lemma_71_17_2_ReesProj
public import stacks_project.Chap71.Lemma_71_17_2_Comparison

/-!
# Lemma 71.17.2

The blowup of an algebraic space in a quasi-coherent ideal sheaf is, on affine
étale charts, the homogeneous spectrum of the corresponding Rees algebra, and
that spectrum is covered by spectra of affine blowup algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The Twist atlas identification of the étale base change of a blowup with the
local relative Proj. -/
def affineEtaleAtlasIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) :
    pullback π.reesTwist.atlas.hom π.hom ≅
      ofOver (localCoverOver π.reesTwist.atlas π.reesTwist.localScheme
        π.reesTwist.localπ) :=
  spacesEtalePullbackInclusionSpaceIso π.hom π.reesTwist.atlas ≪≫
    π.reesTwist.localIso

/-- `affineEtaleAtlasIso` is the spaces-étale comparison followed by the Twist
local identification. -/
theorem affineEtaleAtlasIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) :
    affineEtaleAtlasIso π =
      spacesEtalePullbackInclusionSpaceIso π.hom π.reesTwist.atlas ≪≫
        π.reesTwist.localIso :=
  sorry

/-- Lemma 71.17.2 (1): let `S` be a scheme, let `X` be an algebraic space over
`S`, let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals, let `U` be an affine
scheme étale over `X`, and let `π : X' ⟶ X` be the blowup of `X` in `I`. Then
the comparison `affineComparisonHom π U : U ×_X X' ⟶ Proj(⊕_{d ≥ 0} I_A ^ d)`
is an isomorphism of algebraic spaces over `U`, where
`I_A = correspondingIdeal I U` is the ideal of `A = Γ(U, ⊤)` corresponding to
`I|_U` and the right-hand side is the homogeneous spectrum of the Rees algebra
of `I_A`. The over-`U` triangle is `affineComparisonHom_over`. -/
@[stacks 085R]
theorem affineEtaleIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    IsIso (affineComparisonHom π U) :=
  sorry

/-- Lemma 71.17.2 (2): moreover, the identified `Proj(⊕ I_A ^ d)` has an affine
open covering by spectra of the affine blowup algebras `A[I_A / a]`, namely the
images of `Spec (affineBlowupChart (correspondingIdeal I U) a)` along
`ofOverMap (affineChartOverHom I U a)`. -/
@[stacks 085R]
theorem existsAffineOpenCoverByBlowupCharts {S : Scheme.{u}}
    {X : AlgebraicSpace S} {I : IdealSubobject X} [IsQuasiCoherent I]
    (U : affineEtaleSite X) :
    IsZariskiCover (ofOver (reesProjOver I U))
      (fun a : correspondingIdeal I U ↦
        ofOver (Over.mk (affineChartToU I U a ≫ U.obj.left.hom)))
      (fun a ↦ ofOverMap (affineChartOverHom I U a)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
