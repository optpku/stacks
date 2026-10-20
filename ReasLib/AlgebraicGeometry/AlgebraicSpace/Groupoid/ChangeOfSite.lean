module

public import ReasLib.CategoryTheory.Sites.SheafGroupoid.ChangeOfSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfSite

/-!
# Quotient stacks under enlargement of chosen big fppf sites

A scheme-compatible inclusion of chosen big fppf sites preserves algebraic-space
sheaves under inverse image. The internal sheaf-groupoid comparison therefore
specializes to quotient stacks of groupoids in algebraic spaces on these sites.
-/

@[expose] public section

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigFppfSite

open CategoryTheory Limits

/-- Inverse image preserves the algebraicity of the base, object, and arrow
sheaves of a groupoid in algebraic spaces on a chosen big fppf site. -/
theorem inverseImage_groupoid_isAlgebraicSpace
    (𝒮 𝒯 : ChosenBigFppfSite.{u, v}) (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
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
    (B : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (G : SheafGroupoid (𝒮.bigTopology S) B)
    [IsAlgebraicSpace B] [IsAlgebraicSpace G.U.left] [IsAlgebraicSpace G.R.left] :
    IsAlgebraicSpace
        (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj B) ∧
      IsAlgebraicSpace
        ((SheafGroupoid.inverseImage (Over.post (X := S) inclusion)
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)) G).U.left) ∧
      IsAlgebraicSpace
        ((SheafGroupoid.inverseImage (Over.post (X := S) inclusion)
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)) G).R.left) :=
  ⟨inverseImage_isAlgebraicSpace 𝒮 𝒯 inclusion e S B,
    inverseImage_isAlgebraicSpace 𝒮 𝒯 inclusion e S G.U.left,
    inverseImage_isAlgebraicSpace 𝒮 𝒯 inclusion e S G.R.left⟩

/-- The canonical comparison from the inverse image of an algebraic-space
groupoid quotient to the quotient of its inverse-image groupoid on a larger
chosen big fppf site. -/
def quotientStackInverseImageHom
    (𝒮 𝒯 : ChosenBigFppfSite.{u, v}) (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
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
    [IsAlgebraicSpace B] [IsAlgebraicSpace G.U.left] [IsAlgebraicSpace G.R.left] :
    CartesianBasedFunctor
      (SheafGroupoid.quotientInverseImage (Over.post (X := S) inclusion)
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)) G).target.p
      (SheafGroupoid.inverseImage (Over.post (X := S) inclusion)
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)) G).quotientStack.p :=
  SheafGroupoid.quotientStackInverseImageHom (Over.post (X := S) inclusion)
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)) G

/-- For a scheme-compatible fully faithful inclusion of chosen big fppf sites,
the canonical comparison between inverse image of a groupoid quotient stack
and quotient of the inverse-image algebraic-space groupoid has a quasi-inverse
over the larger slice site. -/
theorem quotientStackInverseImage_equivalence
    (𝒮 𝒯 : ChosenBigFppfSite.{u, v}) (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
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
    [IsAlgebraicSpace B] [IsAlgebraicSpace G.U.left] [IsAlgebraicSpace G.R.left] :
    Nonempty (BasedFunctor.QuasiInverse
      (quotientStackInverseImageHom 𝒮 𝒯 inclusion e S B G).toBasedFunctor) :=
  SheafGroupoid.quotientStackInverseImage_equivalence (Over.post (X := S) inclusion)
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)) G

end AlgebraicGeometry.ChosenBigFppfSite
