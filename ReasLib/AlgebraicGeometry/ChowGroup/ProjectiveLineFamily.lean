/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.ProjectiveLineFamily

/-- The degree-`k` cycle associated to the zero image of a projective-line family. -/
noncomputable def zeroCycle {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (k : ℤ) (W : (space X).IdealSheafData) :
    CycleGroup X.left (X.hom.relativeDimensionFunction delta) k :=
  @Scheme.IdealSheafData.associatedCycle X.left
    (LocallyOfFiniteType.isLocallyNoetherian X.hom) (zeroImage X W)
      (X.hom.relativeDimensionFunction delta) k

/-- The zero endpoint cycle is the associated cycle of the zero image. -/
theorem zeroCycle_def {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (k : ℤ) (W : (space X).IdealSheafData) :
    zeroCycle delta X k W = @Scheme.IdealSheafData.associatedCycle X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom) (zeroImage X W)
        (X.hom.relativeDimensionFunction delta) k := sorry

/-- The degree-`k` cycle associated to the infinity image of a projective-line family. -/
noncomputable def infinityCycle {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (k : ℤ) (W : (space X).IdealSheafData) :
    CycleGroup X.left (X.hom.relativeDimensionFunction delta) k :=
  @Scheme.IdealSheafData.associatedCycle X.left
    (LocallyOfFiniteType.isLocallyNoetherian X.hom) (infinityImage X W)
      (X.hom.relativeDimensionFunction delta) k

/-- The infinity endpoint cycle is the associated cycle of the infinity image. -/
theorem infinityCycle_def {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (k : ℤ) (W : (space X).IdealSheafData) :
    infinityCycle delta X k W = @Scheme.IdealSheafData.associatedCycle X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom) (infinityImage X W)
        (X.hom.relativeDimensionFunction delta) k := sorry

/-- Endpoint-cycle differences have locally finite supports when the original family of closed
subschemes has locally finite supports. -/
theorem fiberDifferencesLocallyFinite {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (k : ℤ) {I : Type v}
    (W : I → (space X).IdealSheafData)
    (h_local : LocallyFinite fun i ↦ ((W i).support : Set (space X))) :
    LocallyFinite fun i ↦
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction delta) k
        (zeroCycle delta X k (W i) - infinityCycle delta X k (W i))).support := sorry

/-- The locally finite sum of the zero endpoint cycles minus the infinity endpoint cycles. -/
noncomputable def boundary {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (k : ℤ) {I : Type v}
    (W : I → (space X).IdealSheafData)
    (h_local : LocallyFinite fun i ↦ ((W i).support : Set (space X))) :
    CycleGroup X.left (X.hom.relativeDimensionFunction delta) k :=
  CycleGroup.locallyFiniteSum (X.hom.relativeDimensionFunction delta) k
    (fun i ↦ zeroCycle delta X k (W i) - infinityCycle delta X k (W i))
    (fiberDifferencesLocallyFinite delta X k W h_local)

/-- The boundary is the canonical locally finite sum of its endpoint-cycle differences. -/
theorem boundary_def {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (k : ℤ) {I : Type v}
    (W : I → (space X).IdealSheafData)
    (h_local : LocallyFinite fun i ↦ ((W i).support : Set (space X))) :
    boundary delta X k W h_local =
      CycleGroup.locallyFiniteSum (X.hom.relativeDimensionFunction delta) k
        (fun i ↦ zeroCycle delta X k (W i) - infinityCycle delta X k (W i))
        (fiberDifferencesLocallyFinite delta X k W h_local) := sorry

/-- The degree-`k` cycles of the zero and infinity fibers, viewed as closed subschemes of `X`,
are rationally equivalent. -/
theorem zeroCycle_rationallyEquivalent_infinityCycle
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
    @RationalEquivalence.RationallyEquivalent X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance k
      (zeroCycle delta X k W) (infinityCycle delta X k W) := sorry

/-- A locally finite family of integral projective-line families of the prescribed relative
dimension has rationally trivial endpoint boundary. -/
theorem boundary_rationallyEquivalent_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
    {I : Type u} (W : I → (space X).IdealSheafData)
    (h_integral : ∀ i, IsIntegral (W i).subscheme)
    (h_dimension : ∀ i,
      (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom).closedSubschemeDeltaDimension
        delta (W i) = ((k + 1 : ℤ) : EInt))
    (h_zero : ∀ i, ¬ ((W i).support : Set (space X)) ⊆
      (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
        (ProjectiveLine.Relative.zeroDivisor S).support)
    (h_infinity : ∀ i, ¬ ((W i).support : Set (space X)) ⊆
      (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
        (ProjectiveLine.Relative.infinityDivisor S).support)
    (h_local : LocallyFinite fun i ↦ ((W i).support : Set (space X))) :
    @RationalEquivalence.RationallyEquivalent X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance k
      (boundary delta X k W h_local) 0 := sorry

/-- Every degree-`k` cycle rationally equivalent to zero is the locally finite boundary of
integral projective-line families of relative dimension `k + 1`, none contained in an endpoint
fiber. -/
theorem exists_boundary_eq_of_rationallyEquivalent_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction delta) k)
    (h_alpha : @RationalEquivalence.RationallyEquivalent X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance k alpha 0) :
    ∃ (I : Type u) (W : I → (space X).IdealSheafData),
      (∀ i, IsIntegral (W i).subscheme) ∧
      (∀ i, (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom).closedSubschemeDeltaDimension
        delta (W i) = ((k + 1 : ℤ) : EInt)) ∧
      (∀ i, ¬ ((W i).support : Set (space X)) ⊆
        (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
          (ProjectiveLine.Relative.zeroDivisor S).support) ∧
      (∀ i, ¬ ((W i).support : Set (space X)) ⊆
        (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
          (ProjectiveLine.Relative.infinityDivisor S).support) ∧
      ∃ h_local : LocallyFinite fun i ↦ ((W i).support : Set (space X)),
        alpha = boundary delta X k W h_local := sorry

end AlgebraicGeometry.ProjectiveLineFamily
