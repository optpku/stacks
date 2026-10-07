module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Laurent
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
public import ReasLib.Topology.OpenCover.Refinement

/-!
# Two-chart identity glueing of the affine line with doubled origin

The source cover `𝒰` is the pair of affine charts of `scheme k 1`, with overlap immersions both
given by the identity glueing `x ↦ z` and `y ↦ z`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.DoubledOrigin CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry LaurentPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

variable (k : Type u) [Field k]

/-- The two-chart open covering `𝒰 : X = U₁ ∪ U₂` of the affine line with doubled origin, with
`Uᵢ = chart k 1 i ≅ Spec k[x]` and `Spec k[y]` respectively. -/
def chartCover : Fin 2 → (scheme k 1).Opens :=
  chart k 1

/-- The source covering condition `X = U₁ ∪ U₂`. -/
theorem chartCover_isOpenCover : IsOpenCover (chartCover k) :=
  sorry

/-- Universe-lifted indexing of `chartCover`, as required by `moduleCechCohomology`. -/
def chartCoverULift : ULift.{u} (Fin 2) → (scheme k 1).Opens :=
  fun i ↦ chartCover k i.down

/-- The universe-lifted two-chart family still covers the doubled line. -/
theorem chartCoverULift_isOpenCover : IsOpenCover (chartCoverULift k) :=
  sorry

/-- The bundled two-chart open cover of the underlying topological space. -/
def chartOpenCover : OpenCover.{u} (scheme k 1).carrier :=
  OpenCover.ofFamily (chartCoverULift k) (chartCoverULift_isOpenCover k)

/-- The bundled cover evaluates to the universe-lifted two-chart family. -/
theorem chartOpenCover_obj (i : ULift.{u} (Fin 2)) :
    chartOpenCover k i = chartCoverULift k i :=
  sorry

/-- The overlap `U₁ ∩ U₂` of the two affine charts. -/
abbrev chartOverlap : (scheme k 1).Opens :=
  chartCover k 0 ⊓ chartCover k 1

/-- Restriction of sections from the first chart `U₁ ≅ Spec k[x]` to the overlap. -/
def leftRestriction :
    Γ(scheme k 1, chartCover k 0) →+* Γ(scheme k 1, chartOverlap k) :=
  ((scheme k 1).presheaf.map
      (homOfLE (inf_le_left : chartOverlap k ≤ chartCover k 0)).op).hom

/-- Restriction of sections from the second chart `U₂ ≅ Spec k[y]` to the overlap. -/
def rightRestriction :
    Γ(scheme k 1, chartCover k 1) →+* Γ(scheme k 1, chartOverlap k) :=
  ((scheme k 1).presheaf.map
      (homOfLE (inf_le_right : chartOverlap k ≤ chartCover k 1)).op).hom

/-- Restriction from the first chart preserves `1`. -/
theorem leftRestriction_map_one : leftRestriction k 1 = 1 :=
  sorry

/-- Restriction from the second chart preserves `1`. -/
theorem rightRestriction_map_one : rightRestriction k 1 = 1 :=
  sorry

/-- Both overlap immersions are the identity glueing `x ↦ z` and `y ↦ z`, i.e. the canonical
map `k[X] → k[T;T⁻¹]`. -/
abbrev overlapRingHom : Polynomial k →+* LaurentPolynomial k :=
  Polynomial.toLaurent

/-- The coordinate ring of each affine chart is canonically `k[X]`. -/
def chartCoordinateAlgEquiv : coordinateRing k 1 ≃ₐ[k] Polynomial k :=
  MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))

/-- The overlap ring homomorphism sends the polynomial generator to `T`. -/
theorem overlapRingHom_X : overlapRingHom k Polynomial.X = LaurentPolynomial.T 1 :=
  sorry

/-- The unique coordinate on affine 1-space is sent to the polynomial generator `X`. -/
theorem chartCoordinateAlgEquiv_coordinate :
    chartCoordinateAlgEquiv k (coordinate k 1 0) = Polynomial.X :=
  sorry

/-- The canonical identification of sections on the `i`-th affine chart with `k[X]`, via
`chartIso`, `coordinateRingGlobalSectionsIso`, and `chartCoordinateAlgEquiv`. -/
def chartCoordinateRingHom (i : Fin 2) :
    Polynomial k →+* Γ(scheme k 1, chartCover k i) :=
  (CommRingCat.Hom.hom
      (PuncturedAffineSpace.coordinateRingToGlobalSections (ULift.{u} (Fin 1)) k ≫
        (chartIso k 1 i).hom.appTop ≫ (chart k 1 i).topIso.hom)).comp
    (chartCoordinateAlgEquiv k).symm.toRingHom

/-- The chart coordinate identification preserves `1`. -/
theorem chartCoordinateRingHom_map_one (i : Fin 2) :
    chartCoordinateRingHom k i 1 = 1 :=
  sorry

/-- The chart coordinate identification sends `X` to the image of the unique affine coordinate. -/
theorem chartCoordinateRingHom_X (i : Fin 2) :
    chartCoordinateRingHom k i Polynomial.X =
      chartCoordinateRingHom k i (chartCoordinateAlgEquiv k (coordinate k 1 0)) :=
  sorry

/-- There is a ring identification of overlap sections with Laurent polynomials intertwining both
chart restrictions with `Polynomial.toLaurent` after `chartIso` and `chartCoordinateAlgEquiv`. -/
theorem exists_identityGlueingRingEquiv :
    ∃ e : Γ(scheme k 1, chartOverlap k) ≃+* LaurentPolynomial k,
      (∀ p : Polynomial k,
          e (leftRestriction k (chartCoordinateRingHom k 0 p)) = Polynomial.toLaurent p) ∧
      (∀ p : Polynomial k,
          e (rightRestriction k (chartCoordinateRingHom k 1 p)) = Polynomial.toLaurent p) :=
  sorry

/-- The first chart of `chartCover` is the canonical chart `chart k 1 0`. -/
theorem chartCover_zero : chartCover k 0 = chart k 1 0 :=
  sorry

/-- The second chart of `chartCover` is the canonical chart `chart k 1 1`. -/
theorem chartCover_one : chartCover k 1 = chart k 1 1 :=
  sorry

/-- Universe-lifted indexing recovers `chartCover`. -/
theorem chartCoverULift_down (i : ULift.{u} (Fin 2)) :
    chartCoverULift k i = chartCover k i.down :=
  sorry

end AlgebraicGeometry.DoubledOrigin
