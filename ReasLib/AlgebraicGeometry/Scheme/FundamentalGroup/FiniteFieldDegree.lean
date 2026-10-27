/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.Finite.Extension
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.DegreeExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualGaloisModule
public import ReasLib.FieldTheory.Finite.ArithmeticFrobenius

/-!
# Finite-field degree maps

Finite extension test covers determine the geometric-Frobenius-normalized
continuous degree map and its arithmetic fundamental-group extension.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.SchemeOverField
open scoped Topology
noncomputable section
universe u

namespace ProfiniteGrp.DegreeExtension

/-- The spectrum map of a finite field extension is finite. -/
theorem specFieldExtension_finite {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] :
    AlgebraicGeometry.IsFinite
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := sorry

/-- The spectrum map of a finite separable field extension is étale. -/
theorem specFieldExtension_etale {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap k L))) := sorry

/-- The finite étale cover attached to the specified finite separable field. -/
noncomputable def specFieldExtensionCover (k L : Type u) [Field k] [Field L]
    [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    FiniteEtale (Spec (CommRingCat.of k)) :=
  { toComma := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    prop := ⟨specFieldExtension_finite, specFieldExtension_etale⟩ }

/-- The geometric point of a field cover is its specified embedding. -/
noncomputable def specFieldExtensionPoint {k L : Type u} [Field k] [Field L]
    [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (e : L →ₐ[k] AlgebraicClosure k) :
    (specFieldGeometricPoint k (AlgebraicClosure k)).finiteFiber.obj (specFieldExtensionCover k L) :=
  Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) (w := sorry)

/-- The image of arithmetic Frobenius in `π₁(Spec k)` at the canonical algebraic-closure
geometric point. -/
noncomputable def arithmeticFrobeniusπ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k)) :=
  galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) (FiniteField.arithmeticFrobenius k)

/-- Arithmetic Frobenius at the field-spectrum image of a geometric basepoint. -/
noncomputable def arithmeticFrobeniusπAt {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) :
    etaleFundamentalGroup (Spec (CommRingCat.of k))
      (galoisPoint X (arithmeticPoint X η)) :=
  GeometricPoint.autHom (specFiberFunctorIso X η) (arithmeticFrobeniusπ (k := k))

/-- `arithmeticFrobeniusπ` is the image of `FiniteField.arithmeticFrobenius k`. -/
theorem arithmeticFrobeniusπ_spec {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    arithmeticFrobeniusπ (k := k) =
      galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) (FiniteField.arithmeticFrobenius k) :=
  sorry

/-- Geometric Frobenius in `π₁(Spec k)` at the canonical algebraic-closure geometric
point: the inverse of arithmetic Frobenius, equivalently the image of
`(FiniteField.arithmeticFrobenius k)⁻¹`. -/
noncomputable def geometricFrobeniusπ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k)) :=
  (arithmeticFrobeniusπ (k := k))⁻¹

/-- Geometric Frobenius at the field-spectrum image of a geometric basepoint. -/
noncomputable def geometricFrobeniusπAt {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) :
    etaleFundamentalGroup (Spec (CommRingCat.of k))
      (galoisPoint X (arithmeticPoint X η)) :=
  GeometricPoint.autHom (specFiberFunctorIso X η) (geometricFrobeniusπ (k := k))

/-- `geometricFrobeniusπ` is the image of `(FiniteField.arithmeticFrobenius k)⁻¹`. -/
theorem geometricFrobeniusπ_spec {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    geometricFrobeniusπ (k := k) =
      galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)
        (FiniteField.arithmeticFrobenius k)⁻¹ :=
  sorry

/-- `geometricFrobeniusπ` is the inverse of `arithmeticFrobeniusπ`. -/
theorem geometricFrobeniusπ_eq_inv {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    geometricFrobeniusπ (k := k) = (arithmeticFrobeniusπ (k := k))⁻¹ :=
  sorry

/-- A finite quotient coordinate of the degree map. -/
abbrev SpecDegreeQuotient (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :=
  integerGroup.{u + 1} ⧸ H.toSubgroup

/-- The testing field has the degree of the actual finite quotient. -/
noncomputable abbrev specDegreeField (k : Type u) [Field k] [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) : Type u :=
  ULift.{u} (FiniteField.Extension k p H.toSubgroup.index)

/-- The finite-field spectrum used to read one residue of the degree map. -/
noncomputable def specDegreeCover (k : Type u) [Field k] [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    FiniteEtale (Spec (CommRingCat.of k)) := by
  -- Local instance justification (defeq pin): bind the nonzero quotient index required by the finite extension algebra.
  letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
  exact specFieldExtensionCover k (specDegreeField k p H)

/-- A canonical library field embedding supplies the test point. -/
noncomputable def specDegreePoint (k : Type u) [Field k] [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    (specFieldGeometricPoint k (AlgebraicClosure k)).finiteFiber.obj (specDegreeCover k p H) := by
  -- Local instance justification (defeq pin): bind the nonzero quotient index required by the finite extension algebra.
  letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
  exact specFieldExtensionPoint (IsAlgClosed.lift : specDegreeField k p H →ₐ[k] AlgebraicClosure k)

/-- Read the geometric Frobenius exponent by evaluating the finite orbit of a test point. -/
noncomputable def specDegreeCoordinate {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1})
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k))) :
    SpecDegreeQuotient H := by
  classical
  exact ∏ j : Fin H.toSubgroup.index,
    if σ.hom.app (specDegreeCover k p H) (specDegreePoint k p H) =
        (geometricFrobeniusπ (k := k) ^ j.val).hom.app
          (specDegreeCover k p H) (specDegreePoint k p H)
    then QuotientGroup.mk (Multiplicative.ofAdd (ULift.up (j.val : ℤ)))
    else 1

/-- Naturality of fiber automorphisms makes the finite quotient coordinates compatible. -/
theorem specDegreeCoordinate_naturality {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    {H L : FiniteIndexNormalSubgroup integerGroup.{u + 1}} (f : H ⟶ L)
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k))) :
    (ProfiniteCompletion.diagram integerGroup).map f (specDegreeCoordinate H σ) =
      specDegreeCoordinate L σ := sorry

/-- The degree is the actual compatible tuple of finite-field evaluations. -/
noncomputable def specDegreeTuple {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k))) :
    hatZ.{u + 1} :=
  ⟨fun H ↦ specDegreeCoordinate H σ, fun _ _ f ↦ specDegreeCoordinate_naturality f σ⟩

/-- The residue of the degree tuple is its specified finite-field computation. -/
@[simp]
theorem specDegreeTuple_apply {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k)))
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    (specDegreeTuple σ).val H = specDegreeCoordinate H σ := rfl


/-- Existence and uniqueness of the continuous surjection `π₁(Spec k) ⟶ hatZ` sending
geometric Frobenius to `1`. -/
theorem existsUnique_specToHatZ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    ∃! f : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k)) ⟶
        hatZ.{u + 1},
      Function.Surjective f ∧ f (geometricFrobeniusπ (k := k)) = hatZOne.{u + 1} :=
  sorry

/-- The unique continuous surjection `π₁(Spec k) ⟶ hatZ` sending geometric Frobenius to
the generator `1`. -/
noncomputable def specToHatZ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k)) ⟶
      hatZ.{u + 1} :=
  let laws : specDegreeTuple (k := k) 1 = 1 ∧
      (∀ a b, specDegreeTuple (k := k) (a * b) = specDegreeTuple a * specDegreeTuple b) ∧
      Continuous (specDegreeTuple (k := k)) := sorry
  ProfiniteGrp.ofHom
    { toFun := specDegreeTuple
      map_one' := laws.1
      map_mul' := laws.2.1
      continuous_toFun := laws.2.2 }

/-- Each finite quotient coordinate of the degree map is its finite-orbit evaluation. -/
@[simp]
theorem specToHatZ_apply {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k)))
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    (specToHatZ (k := k) σ).val H = specDegreeCoordinate H σ := rfl

/-- The degree map at a general geometric point, obtained by transporting `specToHatZ`
along the fiber identification. -/
noncomputable def specToHatZAt {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) :
    etaleFundamentalGroup (Spec (CommRingCat.of k))
      (galoisPoint X (arithmeticPoint X η)) ⟶ hatZ.{u + 1} :=
  ProfiniteGrp.ofHom (GeometricPoint.autHom (specFiberFunctorIso X η).symm) ≫
    specToHatZ (k := k)

/-- The degree map `π₁(Spec k) ⟶ hatZ` is surjective. -/
theorem specToHatZ_surjective {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    Function.Surjective (specToHatZ (k := k)) :=
  sorry

/-- `specToHatZ` sends geometric Frobenius to the generator `1` of `hatZ`. -/
theorem specToHatZ_geometricFrobenius {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    specToHatZ (k := k) (geometricFrobeniusπ (k := k)) = hatZOne.{u + 1} :=
  sorry

/-- `specToHatZAt` sends the transported geometric Frobenius to `1`. -/
theorem specToHatZAt_geometricFrobenius {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) :
    specToHatZAt X η (geometricFrobeniusπAt X η) = hatZOne.{u + 1} :=
  sorry

/-- A continuous surjection `π₁(Spec k) ⟶ hatZ` sending geometric Frobenius to `1`
equals `specToHatZ`. -/
theorem specToHatZ_unique {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (f : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specFieldGeometricPoint k (AlgebraicClosure k)) ⟶
      hatZ.{u + 1})
    (hf : Function.Surjective f)
    (hF : f (geometricFrobeniusπ (k := k)) = hatZOne.{u + 1}) :
    f = specToHatZ (k := k) :=
  sorry

/-- Geometric connectedness makes the arithmetic projection, and hence the normalized
finite-field degree map, surjective. -/
theorem geometricDegree_surjective {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) :
    Function.Surjective
      (arithmeticToGalois X (arithmeticPoint X η) ≫ specToHatZAt X η) := sorry

/-- The étale fundamental group of a geometrically connected scheme over a finite
field, as a degree extension of `hatZ`. The degree map is `arithmeticToGalois`
followed by the unique geometric-Frobenius-normalized map `specToHatZAt`. -/
noncomputable def ofEtaleFundamentalGroup {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) : DegreeExtension.{u + 1} where
  middle := etaleFundamentalGroup X.left (arithmeticPoint X η)
  deg := arithmeticToGalois X (arithmeticPoint X η) ≫ specToHatZAt X η
  deg_surjective := geometricDegree_surjective X η

/-- Unfolding of `ofEtaleFundamentalGroup` on the middle group. -/
theorem ofEtaleFundamentalGroup_middle {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) :
    (ofEtaleFundamentalGroup X η).middle = etaleFundamentalGroup X.left (arithmeticPoint X η) :=
  sorry

/-- Unfolding of `ofEtaleFundamentalGroup.deg` as `arithmeticToGalois` followed by
`specToHatZAt`. -/
theorem ofEtaleFundamentalGroup_deg {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)) :
    (ofEtaleFundamentalGroup X η).deg =
      arithmeticToGalois X (arithmeticPoint X η) ≫ specToHatZAt X η :=
  sorry


end ProfiniteGrp.DegreeExtension
