module

public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import stacks_project.Chap76.Lemma_76_17_2_Comparison

/-!
# Perturbations of morphisms of first-order thickenings of algebraic spaces

An `𝒪_X`-linear map `θ : a^* Ω_{Y/B} ⟶ C_{X/X'}` determines the `𝒪_B`-derivation
`D = d_{Y/B} ∘ θ` into `a_* C_{X/X'}`, and thereby a unique perturbation of a
morphism of first-order thickenings over `B` with `(a')^♯ - (b')^♯ = D`.

Here `Ω_{Y/B}` and `d_{Y/B}` are the canonical ringed-topos differentials.
The specified inverse-image comparison changes only the relative-base
certificate when using the real conormal maps of Lemma 76.17.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open PresheafOfModules.DifferentialsConstruction
noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}}

/-- The `𝒪_B`-derivation `D = d_{Y/B} ∘ θ` associated to an `𝒪_X`-linear map
`θ : a^* Ω_{Y/B} ⟶ F`, obtained by postcomposing `d_{Y/B}` with the adjunct of
`θ`. -/
def derivationOfPullback {Y B X : AlgebraicSpace S} (hY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (θ : (Modules.pullback a).obj (relativeDifferentials hY) ⟶ F) :
    Hom.derivations hY ((Modules.pushforward a).obj F) :=
  (universalDerivation hY).postcomp
    ((SheafOfModules.forget (structureSheaf Y) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf Y).obj)).map
      ((Modules.pullbackPushforwardAdjunction a).homEquiv _ _ θ))

/-- Unfolding of `derivationOfPullback`. -/
theorem derivationOfPullback_eq {Y B X : AlgebraicSpace S} (hY : Y ⟶ B)
    (a : X ⟶ Y) {F : X.Modules}
    (θ : (Modules.pullback a).obj (relativeDifferentials hY) ⟶ F) :
    derivationOfPullback hY a θ =
      (universalDerivation hY).postcomp
        ((SheafOfModules.forget (structureSheaf Y) ⋙
            PresheafOfModules.restrictScalars (𝟙 (structureSheaf Y).obj)).map
          ((Modules.pullbackPushforwardAdjunction a).homEquiv _ _ θ)) :=
  rfl

/-- Equation 76.17.1.1 inverted: canonical universal descent, followed by the
pullback–pushforward adjunction, recovers `θ`. The site-generic owner is
specialized to the canonical structure map, preserving the same differentials. -/
theorem derivationOfPullback_spec {Y B X : AlgebraicSpace S} (hY : Y ⟶ B)
    (a : X ⟶ Y) {F : X.Modules}
    (θ : (Modules.pullback a).obj (relativeDifferentials hY) ⟶ F) :
    ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F).symm
      (SheafOfModules.RingedSite.relativeDifferentialDesc.{u + 1, u, u}
        (commInverseImageStructureSheafMap hY) (F := (Modules.pushforward a).obj F)
        (derivationOfPullback hY a θ)) = θ := by
  change ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F).symm
    (SheafOfModules.RingedSite.relativeDifferentialDesc.{u + 1, u, u}
      (commInverseImageStructureSheafMap hY)
      (F := (Modules.pushforward a).obj F)
      ((SheafOfModules.RingedSite.relativeDifferential.{u + 1, u, u}
        (commInverseImageStructureSheafMap hY)).postcomp
          (((Modules.pullbackPushforwardAdjunction a).homEquiv
            (Hom.relativeDifferentials hY) F θ).val))) = θ
  exact (congrArg
    ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F).symm
    (SheafOfModules.RingedSite.RelativeDifferentials.desc_postcomp_relativeDifferential
      (commInverseImageStructureSheafMap hY)
      ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F θ))).trans
        (Equiv.symm_apply_apply _ θ)

namespace Deformation

/-- A candidate perturbation of `(a, a')` has the same reduced map `a`, the same
Lemma 76.5.3 conormal comparison, lies over `B`, and the Lemma 76.17.1
derivation satisfies `(a')^♯ - (b')^♯ = D = d_{Y/B} ∘ θ`. -/
def IsPerturbation {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqA : CommSq a iX iY a')
    (θ : (Modules.pullback a).obj (relativeDifferentials sY) ⟶ Hom.conormalSheaf iX)
    (b' : X' ⟶ Y') : Prop :=
  b' ≫ sY' = sX' ∧
    ∃ sqB : CommSq a iX iY b',
      Hom.Conormal.map sqA = Hom.Conormal.map sqB ∧
        structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
          factorizationMap sY iX iY a
            (ofCanonicalDerivation sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))
              (derivationOfPullback sY a θ))

/-- The defining conditions for a perturbation with prescribed differential map. -/
theorem isPerturbation_iff {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqA : CommSq a iX iY a')
    (θ : (Modules.pullback a).obj (relativeDifferentials sY) ⟶ Hom.conormalSheaf iX)
    (b' : X' ⟶ Y') :
    IsPerturbation sY sX' sY' iX iY a a' sqA θ b' ↔
      b' ≫ sY' = sX' ∧
        ∃ sqB : CommSq a iX iY b',
          Hom.Conormal.map sqA = Hom.Conormal.map sqB ∧
            structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
              factorizationMap sY iX iY a
                (ofCanonicalDerivation sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))
                  (derivationOfPullback sY a θ)) :=
  sorry

/-- An `𝒪_X`-linear map `θ : a^* Ω_{Y/B} ⟶ C_{X/X'}` uniquely determines a
perturbation of a morphism of first-order thickenings over `B`. -/
theorem existsUnique_perturbation {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (sqA : CommSq a iX iY a')
    (θ : (Modules.pullback a).obj (relativeDifferentials sY) ⟶ Hom.conormalSheaf iX) :
    ExistsUnique fun b' : X' ⟶ Y' ↦
      IsPerturbation sY sX' sY' iX iY a a' sqA θ b' :=
  sorry

end Deformation

end AlgebraicGeometry.AlgebraicSpace.Hom
