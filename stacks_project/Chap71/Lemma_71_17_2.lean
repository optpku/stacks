module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Lemma_71_17_2_ReesProj

/-!
# Lemma 71.17.2

The blowup of an algebraic space in a quasi-coherent ideal sheaf is, on affine
étale charts, the homogeneous spectrum of the corresponding Rees algebra, and
that spectrum is covered by spectra of affine blowup algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The canonical morphism `Proj(oplus I_A ^ d) ⟶ X'` over `X`, independently of
`affineEtaleIso`. It is the covering morphism of the blowup's local relative
Proj, precomposed with the structure morphism of `reesProjOver I U` over `U`. -/
def reesProjClassifying {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    ofOver (reesProjOver I U) ⟶ π.space :=
  ofOverMap (Over.homMk (reesProjToU I U) rfl) ≫
    etaleBaseChangeHom π.hom U.obj

/-- Comparison from the functor-of-points fibre product to the homogeneous
spectrum. -/
def etaleBaseChangeReesProjHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    etaleBaseChangeSpace π.hom U.obj ⟶ ofOver (reesProjOver I U) :=
  etaleBaseChangeSnd π.hom U.obj ≫ ofOverMap (Over.homMk (reesProjToU I U) rfl)

/-- Comparison from the homogeneous spectrum to the functor-of-points fibre
product. -/
def etaleBaseChangeReesProjInv {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    ofOver (reesProjOver I U) ⟶ etaleBaseChangeSpace π.hom U.obj :=
  pullback.lift (reesProjClassifying π U) (reesProjOverToU I U) sorry ≫
    (spacesEtalePullbackInclusionSpaceIso π.hom U.obj).hom

/-- Identification of the functor-of-points fibre product `U ×_X X'` with
`ofOver (reesProjOver I U)`. -/
def etaleBaseChangeReesProjIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    etaleBaseChangeSpace π.hom U.obj ≅ ofOver (reesProjOver I U) where
  hom := etaleBaseChangeReesProjHom π U
  inv := etaleBaseChangeReesProjInv π U
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Lemma 71.17.2 (1): let `S` be a scheme, let `X` be an algebraic space over
`S`, let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals, let `U` be an affine
scheme étale over `X`, and let `π : X' ⟶ X` be the blowup of `X` in `I`. Then
there is a canonical isomorphism `U ×_X X' ≅ Proj(⊕_{d ≥ 0} I_A ^ d)` of
algebraic spaces over `U`, where `I_A = correspondingIdeal I U` is the ideal of
`A = Γ(U, ⊤)` corresponding to `I|_U` and the right-hand side is the
homogeneous spectrum of the Rees algebra of `I_A`. -/
@[stacks 085R]
def affineEtaleIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    pullback U.obj.hom π.hom ≅ ofOver (reesProjOver I U) :=
  (spacesEtalePullbackInclusionSpaceIso π.hom U.obj).trans (etaleBaseChangeReesProjIso π U)

/-- The isomorphism `affineEtaleIso` is an isomorphism of algebraic spaces over
`U`. -/
theorem affineEtaleIso_over {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    (affineEtaleIso π U).hom ≫ reesProjOverToU I U =
      pullback.fst U.obj.hom π.hom :=
  sorry

/-- The canonical morphism `Proj(oplus I_A ^ d) ⟶ X'` over `X`. -/
def reesProjToBlowup {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    ofOver (reesProjOver I U) ⟶ π.space :=
  (affineEtaleIso π U).inv ≫ pullback.snd U.obj.hom π.hom

/-- `reesProjToBlowup` is the second projection of `U ×_X X'` after the
identification with `reesProjOver I U`. -/
theorem reesProjToBlowup_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    reesProjToBlowup π U =
      (affineEtaleIso π U).inv ≫ pullback.snd U.obj.hom π.hom :=
  sorry

/-- `reesProjToBlowup` lies over `X`. -/
theorem reesProjToBlowup_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (U : affineEtaleSite X) :
    reesProjToBlowup π U ≫ π.hom = reesProjToX I U :=
  sorry

/-- Lemma 71.17.2 (2): moreover, `U ×_X X'` has an affine open covering by
spectra of the affine blowup algebras `A[I_A / a]`, equivalently the
homogeneous spectrum `reesProj I U` is covered by
`Spec (affineBlowupChart (correspondingIdeal I U) a)`. -/
@[stacks 085R]
theorem existsAffineOpenCoverByBlowupCharts {S : Scheme.{u}}
    {X : AlgebraicSpace S} {I : IdealSubobject X} [IsQuasiCoherent I]
    (U : affineEtaleSite X) :
    ∃ 𝒰 : (reesProj I U).AffineOpenCover, ∀ i : 𝒰.I₀,
      ∃ a : correspondingIdeal I U,
        Nonempty
          (((𝒰.openCover.f i).opensRange).toScheme ≅
            Spec (.of (affineBlowupChart (correspondingIdeal I U) a))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
