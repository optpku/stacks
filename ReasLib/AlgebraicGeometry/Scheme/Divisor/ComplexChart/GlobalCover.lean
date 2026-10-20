module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.PerfectAtlas

/-!
# The global family of divisor charts subordinate to original perfectness

The data index every valid affine divisor chart subordinate to an input model
open. No chart is selected from a new existence theorem. The refinement-cover
law is the remaining affine-trivialization proof obligation for this fixed
family; it appears only in the Prop-valued covering field.

The Rees pieces, their maps and their overlap-open schemes are actual data.
No transition isomorphism or global glued modification is postulated here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)

/-- All actual affine divisor-complex charts subordinate to an original perfect-model open. -/
abbrev divisorChartIndex :=
  Σ C : graphChartIndex E p D,
    {i : (modelSieve E hE).Arrow // (C.U : Y.Opens) ≤ p ⁻¹ᵁ i.Y}

/-- The geometric chart associated to an index is a projection, not a selected witness. -/
def divisorChart (i : divisorChartIndex E hE p D) : graphChartIndex E p D :=
  i.1

/-- The affine coordinate refinements of the actual local strictly-perfect input models
jointly cover the base. This fixed-family cover law requires the usual affine
trivialization of the finite projective terms and the Cartier equation. It is
proof debt only: no output chart is obtained from this theorem by choice. -/
theorem divisorChart_covering [IsEffectiveCartierDivisor D.subschemeι] (y : Y) :
    ∃ i : divisorChartIndex E hE p D, y ∈ (i.1.U : Y.Opens) := by
  -- Affine localization/trivialization of the original model idempotents and
  -- the Cartier ideal must establish this cover law; no data is selected here.
  sorry

/-- The fixed family forms a scheme open cover with no extra chart input. -/
def divisorChartCover [IsEffectiveCartierDivisor D.subschemeι] : Y.OpenCover :=
  Scheme.Cover.mkOfCovers (divisorChartIndex E hE p D)
    (fun i => (i.1.U : Y.Opens).toScheme)
    (fun i => (i.1.U : Y.Opens).ι)
    (by
      intro y
      obtain ⟨i, hi⟩ := divisorChart_covering E hE p D y
      exact ⟨i, ⟨y, hi⟩, rfl⟩)

/-- The scheme in each cover member is exactly the indexed affine open. -/
theorem divisorChartCover_obj [IsEffectiveCartierDivisor D.subschemeι]
    (i : divisorChartIndex E hE p D) :
    (divisorChartCover E hE p D).X i = (i.1.U : Y.Opens).toScheme := rfl

/-- The map in each cover member is the actual open immersion. -/
theorem divisorChartCover_map [IsEffectiveCartierDivisor D.subschemeι]
    (i : divisorChartIndex E hE p D) :
    (divisorChartCover E hE p D).f i = (i.1.U : Y.Opens).ι := rfl

/-- The member refines its particular input perfect-model open by the actual restriction inclusion. -/
def divisorChartToModel (i : divisorChartIndex E hE p D) :
    (i.1.U : Y.Opens).toScheme ⟶ (pullbackCover E hE p).X i.2.1 :=
  Y.homOfLE i.2.2

/-- The chart-to-model restriction respects the original map to the base. -/
theorem divisorChartToModel_over (i : divisorChartIndex E hE p D) :
    divisorChartToModel E hE p D i ≫ (pullbackCover E hE p).f i.2.1 =
      (i.1.U : Y.Opens).ι := by
  exact Scheme.homOfLE_ι _ _

/-- The whole family of actual Rees projective schemes, produced from the original inputs. -/
def graphPieces : divisorChartIndex E hE p D → Scheme.{u} :=
  fun i => i.1.graphScheme

/-- The whole family of actual structural maps to the original divisor scheme. -/
def graphPieceMaps (i : divisorChartIndex E hE p D) : graphPieces E hE p D i ⟶ Y :=
  i.1.graphHom

/-- A graph piece lies over its actual chart-cover member. -/
def graphPieceToChart [IsEffectiveCartierDivisor D.subschemeι]
    (i : divisorChartIndex E hE p D) :
    graphPieces E hE p D i ⟶ (divisorChartCover E hE p D).X i :=
  i.1.graphToChart

/-- The piece-to-base map factors through its coordinate chart on the nose. -/
theorem graphPieceToChart_over [IsEffectiveCartierDivisor D.subschemeι]
    (i : divisorChartIndex E hE p D) :
    graphPieceToChart E hE p D i ≫ (divisorChartCover E hE p D).f i =
      graphPieceMaps E hE p D i := rfl

/-- The overlap open on one Rees piece is the inverse image of the other chart's open. -/
def graphOverlapOpen (i j : divisorChartIndex E hE p D) : (graphPieces E hE p D i).Opens :=
  graphPieceMaps E hE p D i ⁻¹ᵁ (j.1.U : Y.Opens)

/-- The actual open-overlap scheme before constructing the inter-chart transition isomorphism. -/
def graphOverlap (i j : divisorChartIndex E hE p D) : Scheme.{u} :=
  (graphOverlapOpen E hE p D i j).toScheme

/-- The left overlap inclusion is the canonical open immersion. -/
def graphOverlapLeft (i j : divisorChartIndex E hE p D) :
    graphOverlap E hE p D i j ⟶ graphPieces E hE p D i :=
  (graphOverlapOpen E hE p D i j).ι

/-- The overlap projection to the second chart is the actual restriction of the structural map. -/
def graphOverlapToChart (i j : divisorChartIndex E hE p D) :
    graphOverlap E hE p D i j ⟶ (j.1.U : Y.Opens).toScheme :=
  (graphPieceMaps E hE p D i).resLE (j.1.U : Y.Opens)
    (graphOverlapOpen E hE p D i j) le_rfl

/-- The overlap restriction commutes with the prescribed map to the base. -/
theorem graphOverlapToChart_over (i j : divisorChartIndex E hE p D) :
    graphOverlapToChart E hE p D i j ≫ (j.1.U : Y.Opens).ι =
      graphOverlapLeft E hE p D i j ≫ graphPieceMaps E hE p D i := by
  exact Scheme.Hom.resLE_comp_ι _ _

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
