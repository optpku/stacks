module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.ChangeOfSite
public import stacks_project.Chap78.Lemma_78_28_1_InverseImage
import StacksCheckRecall

/-!
# Quotient stacks and change of big site
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite

universe u v w

/- Lemma 78.28.1. For an inclusion of two big fppf sites and a groupoid
in algebraic spaces over a base sheaf on the smaller slice, the quotient
of the inverse-image groupoid is canonically equivalent to the inverse image
of the quotient stack. The constructed comparison has direction
`f⁻¹[U/R] ⟶ [f⁻¹U/f⁻¹R]`; its based quasi-inverse gives the displayed
source direction `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`. -/
@[stacks 04WX] #check
  (AlgebraicGeometry.ChosenBigFppfSite.quotientStackInverseImage_equivalence :
    ∀ (𝒮 𝒯 : ChosenBigFppfSite.{u, v}) (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
    (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme) (S : 𝒮.carrier)
    [inclusion.Full] [inclusion.Faithful]
    [PreservesLimitsOfShape WalkingCospan inclusion]
    [(Over.post (X := S) inclusion).IsContinuous
      (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
    [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
      (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [HasPullbacks (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]
    [HasPullbacks (Over S)] [HasEqualizers (Over S)]
    [PreservesLimitsOfShape WalkingCospan (Over.post (X := S) inclusion)]
    [PreservesLimitsOfShape WalkingParallelPair (Over.post (X := S) inclusion)]
    [Small.{w} (Over (inclusion.obj S))]
    (B : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (G : SheafGroupoid (𝒮.bigTopology S) B)
    [IsAlgebraicSpace B] [IsAlgebraicSpace G.U.left] [IsAlgebraicSpace G.R.left],
    Nonempty (BasedFunctor.QuasiInverse
      (quotientStackInverseImageHom 𝒮 𝒯 inclusion e S B G).toBasedFunctor))

