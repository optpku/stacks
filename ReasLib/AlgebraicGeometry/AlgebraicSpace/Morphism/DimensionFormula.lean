/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Topology.Defs.Filter
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Dimension formulas for morphisms of algebraic spaces

A flat, locally finite-type morphism of locally Noetherian algebraic spaces
of relative dimension `d` adds `d` to local dimension at every source point.
For a locally finite-type morphism with locally Noetherian target, local-ring
dimension plus residue-field transcendence degree is bounded by the dimension
at the image plus the greatest degree at dimension-zero points specializing to
the source point. This greatest degree exists.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat, locally finite-type morphism of locally Noetherian algebraic spaces
of relative dimension `d` has source dimension at each point equal to the
dimension at its image plus `d`. -/
@[stacks 0AFH]
theorem dimensionAt_eq_image_add_relativeDimension_of_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {d : ℕ} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    [LocallyOfFiniteType f] [RelativeDimension f d] (x : Points X) :
    dimensionAt x = dimensionAt (Points.map f x) + (d : WithBot ℕ∞) :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, the residue-field transcendence degrees at dimension-zero points
specializing to a given point have a greatest natural-number value. -/
theorem exists_isGreatest_residueFieldTrdegAt_specializing
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (x : Points X) :
    ∃ E : ℕ, IsGreatest {n | ∃ ξ : Points X,
      ξ ⤳ x ∧ localRingDimAt ξ = 0 ∧ n = residueFieldTrdegAt f ξ} E :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, the local-ring dimension at a source point plus its residue-field
transcendence degree is at most the local-ring dimension at its image plus the
greatest transcendence degree at dimension-zero points specializing to it. -/
@[stacks 0BAX]
theorem localRingDimAt_add_trdeg_le_genericMax
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (x : Points X) (E : ℕ)
    (hE : IsGreatest {n | ∃ ξ : Points X,
      ξ ⤳ x ∧ localRingDimAt ξ = 0 ∧ n = residueFieldTrdegAt f ξ} E) :
    localRingDimAt x + (residueFieldTrdegAt f x : WithBot ℕ∞) ≤
      localRingDimAt (Points.map f x) + (E : WithBot ℕ∞) :=
  sorry

/-- The supremum of residue-field transcendence degrees of `f` at points of `|X|`
where the local ring of `X` has dimension `0`. -/
noncomputable def localRingDimZeroTrdeg {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : ℕ∞ :=
  ⨆ ξ : Points X, ⨆ _ : localRingDimAt ξ = 0, residueFieldTranscendenceDegreeAt f ξ

/-- The residue-field transcendence degree of `f` at a point of local-ring
dimension `0` is at most `localRingDimZeroTrdeg f`. -/
theorem le_localRingDimZeroTrdeg {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {ξ : Points X} (hξ : localRingDimAt ξ = 0) :
    residueFieldTranscendenceDegreeAt f ξ ≤ localRingDimZeroTrdeg f :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, the dimension of the source is at most the dimension of the target plus
the supremum of residue-field transcendence degrees at source points whose local
rings have dimension zero. -/
@[stacks 0BAY]
theorem dimension_le_add_localRingDimZeroTrdeg
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    dimension X ≤ dimension Y + (localRingDimZeroTrdeg f : WithBot ℕ∞) :=
  sorry

/-- A dominant locally finite-type morphism of integral algebraic spaces with
locally Noetherian target has source dimension bounded by target dimension plus
the residue-field transcendence degree at a generic source point. -/
@[stacks 0EDC]
theorem dimension_le_add_residueFieldTrdegAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Dominant f] [LocallyOfFiniteType f] {x : Points X}
    (hx : x ∈ genericPoints X) :
    dimension X ≤ dimension Y + (residueFieldTrdegAt f x : WithBot ℕ∞) :=
  sorry

/-- A proper dominant morphism of integral algebraic spaces with locally
Noetherian target has source dimension equal to target dimension plus the
residue-field transcendence degree at a generic source point. -/
@[stacks 0EDC]
theorem dimension_eq_add_residueFieldTrdegAt_of_proper {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Dominant f] [Proper f] {x : Points X}
    (hx : x ∈ genericPoints X) :
    dimension X = dimension Y + (residueFieldTrdegAt f x : WithBot ℕ∞) :=
  sorry


namespace Hom

open TopologicalSpace

/-- For a flat morphism of relative dimension `r` over a universally catenary base,
the `δ`-dimension of a nonempty closed inverse image equals the `δ`-dimension of
the closure of the intersection of the closed subset with the morphism's range, plus `r`. -/
theorem closedPreimageDeltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (T : Closeds (Points Y)) (hT : Nonempty (T.preimage (Points.continuous_map f))) :
    closedSetDeltaDimension pX δ (T.preimage (Points.continuous_map f)) =
      closedSetDeltaDimension pY δ
        (Closeds.closure ((T : Set (Points Y)) ∩ Set.range (Points.map f))) + (r : EInt) :=
  sorry

/-- For a flat morphism of relative dimension `r` over a universally catenary base,
the `δ`-dimension of a nonempty closed inverse image is at most the `δ`-dimension
of the closed subset plus `r`. -/
theorem closedPreimageDeltaDimension_le {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (T : Closeds (Points Y)) (hT : Nonempty (T.preimage (Points.continuous_map f))) :
    closedSetDeltaDimension pX δ (T.preimage (Points.continuous_map f)) ≤
      closedSetDeltaDimension pY δ T + (r : EInt) :=
  sorry

/-- A surjective flat morphism of relative dimension `r` over a universally
catenary base shifts the `δ`-dimension of a closed subset with nonempty inverse
image by `r`. -/
theorem closedPreimageDeltaDimension_of_surjective {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] [AlgebraicGeometry.AlgebraicSpace.Surjective f] (hf : f ≫ pY = pX)
    (T : Closeds (Points Y)) (hT : Nonempty (T.preimage (Points.continuous_map f))) :
    closedSetDeltaDimension pX δ (T.preimage (Points.continuous_map f)) =
      closedSetDeltaDimension pY δ T + (r : EInt) :=
  sorry

/-- Every irreducible component of the inverse image of an irreducible closed
subset under a flat morphism of constant relative dimension between good algebraic
spaces over a universally catenary base dominates that subset. -/
theorem componentOfPreimageMapsTo {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : IrreducibleCloseds (Points Y)) (Z' : IrreducibleCloseds (Points X))
    (hZ' : Z' ∈ closedSetIrreducibleComponents
      (Closeds.preimage ⟨Z.carrier, Z.isClosed⟩ (Points.continuous_map f))) :
    IrreducibleCloseds.map (Points.map f) (Points.continuous_map f) Z' = Z :=
  sorry

/-- Every irreducible component of the inverse image of an irreducible closed
subset under a flat morphism of relative dimension `r` between good algebraic
spaces over a universally catenary base has `δ`-dimension shifted by `r`. -/
theorem componentOfPreimageDeltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : IrreducibleCloseds (Points Y)) (Z' : IrreducibleCloseds (Points X))
    (hZ' : Z' ∈ closedSetIrreducibleComponents
      (Closeds.preimage ⟨Z.carrier, Z.isClosed⟩ (Points.continuous_map f))) :
    deltaDimension pX δ Z' = deltaDimension pY δ Z + (r : ℤ) :=
  sorry

/-- For a flat morphism of constant relative dimension between good algebraic
spaces over a universally catenary base, an integral closed subspace whose support
is a component of the inverse image of an integral closed subspace admits a
dominant morphism to that subspace over the ambient morphism. -/
theorem componentOfInverseImage_dominant {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : ClosedSubspace Y) [IsIntegral Z.X] (Z' : ClosedSubspace X)
    [IsIntegral Z'.X]
    (hZ' : ClosedSubspace.irreducibleClosed Z' ∈
      closedSetIrreducibleComponents
        (Closeds.preimage ⟨Z.pointsSet, Z.isClosed_pointsSet⟩
          (Points.continuous_map f))) :
    ∃ g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι ≫ f ∧ Dominant g :=
  sorry

/-- For a flat morphism of relative dimension `r` between good algebraic spaces
over a universally catenary base, an integral closed subspace whose support is a
component of the inverse image of an integral closed subspace has `δ`-dimension
equal to the target subspace's `δ`-dimension plus `r`. -/
theorem componentOfInverseImage_deltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : ClosedSubspace Y) [IsIntegral Z.X] (Z' : ClosedSubspace X)
    [IsIntegral Z'.X]
    (hZ' : ClosedSubspace.irreducibleClosed Z' ∈
      closedSetIrreducibleComponents
        (Closeds.preimage ⟨Z.pointsSet, Z.isClosed_pointsSet⟩
          (Points.continuous_map f))) :
    deltaDimension pX δ (ClosedSubspace.irreducibleClosed Z') =
      deltaDimension pY δ (ClosedSubspace.irreducibleClosed Z) + (r : ℤ) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
