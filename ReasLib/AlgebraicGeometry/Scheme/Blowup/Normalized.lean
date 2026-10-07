module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A normalized blowup of `X` at a closed point: an ordinary point blowup together with the
normalization prerequisites for its source. -/
structure NormalizedBlowup (X : Scheme.{u}) : Type (u + 1) where
  /-- The closed point blown up. -/
  point : closedPoints X
  /-- The source scheme of the ordinary blowup before normalization. -/
  blowupScheme : Scheme.{u}
  /-- The ordinary blowup morphism. -/
  toBlowup : blowupScheme ⟶ X
  /-- The ordinary morphism is the blowup at the reduced closed point. -/
  isBlowup : IsBlowup toBlowup
    (IdealSheafData.vanishingIdeal (PointClosure.closedSubset point.1))
  /-- The generic-point coproduct map of the ordinary blowup is quasi-compact. -/
  quasiCompact : QuasiCompact (genericPointSpectrumCoproductTo blowupScheme)
  /-- The generic-point coproduct map of the ordinary blowup is quasi-separated. -/
  quasiSeparated : QuasiSeparated (genericPointSpectrumCoproductTo blowupScheme)

namespace NormalizedBlowup

/-- Construct a normalized blowup from an ordinary closed-point blowup and the prerequisites for
its normalization. -/
def of {X : Scheme.{u}} (point : closedPoints X) (blowupScheme : Scheme.{u})
    (toBlowup : blowupScheme ⟶ X)
    (isBlowup : IsBlowup toBlowup
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset point.1)))
    (quasiCompact : QuasiCompact (genericPointSpectrumCoproductTo blowupScheme))
    (quasiSeparated : QuasiSeparated (genericPointSpectrumCoproductTo blowupScheme)) :
    NormalizedBlowup X :=
  { point, blowupScheme, toBlowup, isBlowup, quasiCompact, quasiSeparated }

/-- The closed point of a normalized blowup constructed by `of` is the supplied point. -/
theorem of_point {X : Scheme.{u}} (point : closedPoints X) (blowupScheme : Scheme.{u})
    (toBlowup : blowupScheme ⟶ X)
    (isBlowup : IsBlowup toBlowup
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset point.1)))
    (quasiCompact : QuasiCompact (genericPointSpectrumCoproductTo blowupScheme))
    (quasiSeparated : QuasiSeparated (genericPointSpectrumCoproductTo blowupScheme)) :
    (of point blowupScheme toBlowup isBlowup quasiCompact quasiSeparated).point = point := sorry

/-- The ordinary blowup morphism of a normalized blowup constructed by `of` is the supplied
morphism. -/
theorem of_toBlowup {X : Scheme.{u}} (point : closedPoints X) (blowupScheme : Scheme.{u})
    (toBlowup : blowupScheme ⟶ X)
    (isBlowup : IsBlowup toBlowup
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset point.1)))
    (quasiCompact : QuasiCompact (genericPointSpectrumCoproductTo blowupScheme))
    (quasiSeparated : QuasiSeparated (genericPointSpectrumCoproductTo blowupScheme)) :
    (of point blowupScheme toBlowup isBlowup quasiCompact quasiSeparated).toBlowup =
      toBlowup := sorry

/-- The source of a normalized blowup is the canonical normalization of the ordinary blowup
scheme. -/
noncomputable def source {X : Scheme.{u}} (s : NormalizedBlowup X) : Scheme.{u} :=
  @Scheme.normalization s.blowupScheme s.quasiCompact s.quasiSeparated

/-- The source accessor uses the stored normalization prerequisites. -/
theorem source_eq {X : Scheme.{u}} (s : NormalizedBlowup X) :
    s.source = @Scheme.normalization s.blowupScheme s.quasiCompact s.quasiSeparated := sorry

/-- The normalization morphism from the normalized source to the ordinary blowup scheme. -/
noncomputable def toNormalization {X : Scheme.{u}} (s : NormalizedBlowup X) :
    s.source ⟶ s.blowupScheme :=
  @Scheme.normalizationTo s.blowupScheme s.quasiCompact s.quasiSeparated

/-- The normalization morphism accessor is the canonical absolute normalization morphism. -/
theorem toNormalization_def {X : Scheme.{u}} (s : NormalizedBlowup X) :
    s.toNormalization =
      @Scheme.normalizationTo s.blowupScheme s.quasiCompact s.quasiSeparated := sorry

/-- The normalized blowup morphism, obtained by normalization followed by the ordinary blowup. -/
noncomputable def hom {X : Scheme.{u}} (s : NormalizedBlowup X) : s.source ⟶ X :=
  s.toNormalization ≫ s.toBlowup

/-- A normalized blowup morphism is the normalization morphism followed by the ordinary point
blowup. -/
theorem hom_def {X : Scheme.{u}} (s : NormalizedBlowup X) :
    s.hom = s.toNormalization ≫ s.toBlowup := sorry

end NormalizedBlowup

end AlgebraicGeometry.Scheme
