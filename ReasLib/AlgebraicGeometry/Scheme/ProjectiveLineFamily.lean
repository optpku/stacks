module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Divisor
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.MorphismProperties
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/-- The relative product `X ×ₛ ℙ¹ₛ` in which a projective-line family lives. -/
abbrev space {S : Scheme.{u}} (X : Over S) : Scheme.{u} :=
  pullback X.hom (ProjectiveSpace.toBase 1 S)

/-- The inverse image on `W` of the zero divisor of the relative projective line. -/
noncomputable def zeroDivisor {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : W.subscheme.IdealSheafData :=
  (ProjectiveLine.Relative.zeroDivisor S).comap
    (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S))

/-- The zero fiber is the ideal-sheaf pullback of the relative zero divisor. -/
theorem zeroDivisor_def {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    zeroDivisor X W = (ProjectiveLine.Relative.zeroDivisor S).comap
      (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S)) := sorry

/-- The inverse image on `W` of the infinity divisor of the relative projective line. -/
noncomputable def infinityDivisor {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : W.subscheme.IdealSheafData :=
  (ProjectiveLine.Relative.infinityDivisor S).comap
    (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S))

/-- The infinity fiber is the ideal-sheaf pullback of the relative infinity divisor. -/
theorem infinityDivisor_def {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    infinityDivisor X W = (ProjectiveLine.Relative.infinityDivisor S).comap
      (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S)) := sorry

/-- The composite morphism from the zero fiber of `W` to `X`. -/
noncomputable def zeroToX {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : (zeroDivisor X W).subscheme ⟶ X.left :=
  (zeroDivisor X W).subschemeι ≫ W.subschemeι ≫
    pullback.fst X.hom (ProjectiveSpace.toBase 1 S)

/-- The zero-fiber morphism is the composite through `W ⊆ X ×ₛ ℙ¹ₛ`. -/
theorem zeroToX_def {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    zeroToX X W = (zeroDivisor X W).subschemeι ≫ W.subschemeι ≫
      pullback.fst X.hom (ProjectiveSpace.toBase 1 S) := sorry

/-- The composite morphism from the infinity fiber of `W` to `X`. -/
noncomputable def infinityToX {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : (infinityDivisor X W).subscheme ⟶ X.left :=
  (infinityDivisor X W).subschemeι ≫ W.subschemeι ≫
    pullback.fst X.hom (ProjectiveSpace.toBase 1 S)

/-- The infinity-fiber morphism is the composite through `W ⊆ X ×ₛ ℙ¹ₛ`. -/
theorem infinityToX_def {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    infinityToX X W = (infinityDivisor X W).subschemeι ≫ W.subschemeι ≫
      pullback.fst X.hom (ProjectiveSpace.toBase 1 S) := sorry

/-- The zero fiber maps to `X` as a closed immersion. -/
instance instIsClosedImmersionZeroToX {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : IsClosedImmersion (zeroToX X W) := sorry

/-- The infinity fiber maps to `X` as a closed immersion. -/
instance instIsClosedImmersionInfinityToX {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : IsClosedImmersion (infinityToX X W) := sorry

/-- The zero fiber viewed by its scheme-theoretic image as a closed subscheme of `X`. -/
noncomputable def zeroImage {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : X.left.IdealSheafData :=
  (zeroToX X W).ker

/-- The zero image is defined by the kernel of its composite closed immersion into `X`. -/
theorem zeroImage_def {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    zeroImage X W = (zeroToX X W).ker := sorry

/-- The infinity fiber viewed by its scheme-theoretic image as a closed subscheme of `X`. -/
noncomputable def infinityImage {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : X.left.IdealSheafData :=
  (infinityToX X W).ker

/-- The infinity image is defined by the kernel of its composite closed immersion into `X`. -/
theorem infinityImage_def {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    infinityImage X W = (infinityToX X W).ker := sorry

/-- The canonical map from the zero fiber to its scheme-theoretic image is an isomorphism. -/
instance instIsIsoZeroToImage {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : IsIso (zeroToX X W).toImage := sorry

/-- The zero-fiber map factors through the closed subscheme `zeroImage X W`. -/
theorem zeroToImage_imageι {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    (zeroToX X W).toImage ≫ (zeroImage X W).subschemeι = zeroToX X W := sorry

/-- The canonical map from the infinity fiber to its scheme-theoretic image is an isomorphism. -/
instance instIsIsoInfinityToImage {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) : IsIso (infinityToX X W).toImage := sorry

/-- The infinity-fiber map factors through the closed subscheme `infinityImage X W`. -/
theorem infinityToImage_imageι {S : Scheme.{u}} (X : Over S)
    (W : (space X).IdealSheafData) :
    (infinityToX X W).toImage ≫ (infinityImage X W).subschemeι = infinityToX X W := sorry

/-- The zero endpoint divisor pulls back to an effective Cartier divisor on an integral
projective-line family of the prescribed relative dimension that meets neither endpoint. -/
theorem zeroPullbackDefined
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
    (W : (space X).IdealSheafData) [IsIntegral W.subscheme]
    (h_dimension :
      (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom).closedSubschemeDeltaDimension
        delta W = ((k + 1 : ℤ) : EInt))
    (h_zero : ¬ (W.support : Set (space X)) ⊆
      (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
        (ProjectiveLine.Relative.zeroDivisor S).support)
    (h_infinity : ¬ (W.support : Set (space X)) ⊆
      (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
        (ProjectiveLine.Relative.infinityDivisor S).support) :
    Scheme.IdealSheafData.pullbackDefined (ProjectiveLine.Relative.zeroDivisor S)
      (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S)) := sorry

/-- The infinity endpoint divisor pulls back to an effective Cartier divisor on an integral
projective-line family of the prescribed relative dimension that meets neither endpoint. -/
theorem infinityPullbackDefined
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
    (W : (space X).IdealSheafData) [IsIntegral W.subscheme]
    (h_dimension :
      (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom).closedSubschemeDeltaDimension
        delta W = ((k + 1 : ℤ) : EInt))
    (h_zero : ¬ (W.support : Set (space X)) ⊆
      (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
        (ProjectiveLine.Relative.zeroDivisor S).support)
    (h_infinity : ¬ (W.support : Set (space X)) ⊆
      (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
        (ProjectiveLine.Relative.infinityDivisor S).support) :
    Scheme.IdealSheafData.pullbackDefined (ProjectiveLine.Relative.infinityDivisor S)
      (W.subschemeι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S)) := sorry

end AlgebraicGeometry.ProjectiveLineFamily
