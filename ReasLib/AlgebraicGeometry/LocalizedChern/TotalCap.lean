module

public import ReasLib.AlgebraicGeometry.ChowGroup.Rational
public import ReasLib.AlgebraicGeometry.ChowGroup.TotalFundamental
public import ReasLib.AlgebraicGeometry.LocalizedChern.Fundamental
public import ReasLib.AlgebraicGeometry.BivariantClass.Nonnegative.Rational

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

open AlgebraicGeometry.BivariantClass.Nonnegative

namespace AlgebraicGeometry.ChowGroup

/-- Identity-horizontal cap of a homogeneous bivariant class against `[Y]_n`. -/
noncomputable def capOnFundamentalHom {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] (p n : ℤ) :
    @AddMonoidHom
      (BivariantClass δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) p)
      (RelativeChow δ (Over.mk (i ≫ Y.hom)) (n - p))
      (BivariantClass.pointwiseAddCommGroup δ
        (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) p).toAddZeroClass.toAddZero
      inferInstance :=
  @AddMonoidHom.mk' _ _ inferInstance
    (BivariantClass.pointwiseAddCommGroup δ
      (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) p).toAddZeroClass
    (fun c ↦ LocalizedChern.capOnFundamental Y i c n)
    sorry

/-- Evaluation of `capOnFundamentalHom` is `LocalizedChern.capOnFundamental`. -/
theorem capOnFundamentalHom_apply {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] {p n : ℤ}
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) p) :
    capOnFundamentalHom Y i p n c =
      LocalizedChern.capOnFundamental Y i c n :=
  sorry

/-- Cap a completed rational bivariant class with finite Chern support against the
fundamental class of `Y`, landing in `CH_*(X) ⊗ ℚ`. -/
noncomputable def capRationalCompletion {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {Y : Over S} [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] [CompactSpace Y.left]
    (c : Rational.Completion δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y))
    (s : Finset ℕ) : rationalChow δ (Over.mk (i ≫ Y.hom)) :=
  ∑ p ∈ s,
    ∑ n ∈ relativeDimensionDegrees δ Y,
      TensorProduct.map
        (DirectSum.lof ℤ ℤ
          (fun d ↦ RelativeChow δ (Over.mk (i ≫ Y.hom)) d) (n - (p : ℤ)))
        (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
        (@TensorProduct.map ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
          (BivariantClass δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ)) ℚ
          (RelativeChow δ (Over.mk (i ≫ Y.hom)) (n - (p : ℤ))) ℚ
          (BivariantClass.pointwiseAddCommGroup δ
            (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ)).toAddCommMonoid
          inferInstance inferInstance inferInstance
          (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup δ
            (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ)))
          inferInstance inferInstance inferInstance
          (@AddMonoidHom.toIntLinearMap _ _
            (BivariantClass.pointwiseAddCommGroup δ
              (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ))
            inferInstance (capOnFundamentalHom Y i (p : ℤ) n))
          (LinearMap.id : ℚ →ₗ[ℤ] ℚ) (c p))

/-- `capRationalCompletion` is the double sum of identity-horizontal caps of the
finite-support Chern components against `[Y]_n`. -/
theorem capRationalCompletion_def {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {Y : Over S} [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] [CompactSpace Y.left]
    (c : Rational.Completion δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y))
    (s : Finset ℕ) :
    capRationalCompletion δ i c s =
      ∑ p ∈ s,
        ∑ n ∈ relativeDimensionDegrees δ Y,
          TensorProduct.map
            (DirectSum.lof ℤ ℤ
              (fun d ↦ RelativeChow δ (Over.mk (i ≫ Y.hom)) d) (n - (p : ℤ)))
            (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
            (@TensorProduct.map ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
              (BivariantClass δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ)) ℚ
              (RelativeChow δ (Over.mk (i ≫ Y.hom)) (n - (p : ℤ))) ℚ
              (BivariantClass.pointwiseAddCommGroup δ
                (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ)).toAddCommMonoid
              inferInstance inferInstance inferInstance
              (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup δ
                (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ)))
              inferInstance inferInstance inferInstance
              (@AddMonoidHom.toIntLinearMap _ _
                (BivariantClass.pointwiseAddCommGroup δ
                  (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) (p : ℤ))
                inferInstance (capOnFundamentalHom Y i (p : ℤ) n))
              (LinearMap.id : ℚ →ₗ[ℤ] ℚ) (c p)) :=
  sorry

end AlgebraicGeometry.ChowGroup
