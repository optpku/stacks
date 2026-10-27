/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.RelativeCycle.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffinePlaneDegreeTwo

/-- The affine plane `X = 𝔸(2; Spec k)`. -/
abbrev plane (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 2); Spec (.of k))

/-- The structure morphism `X ⟶ Spec k`. -/
abbrev planeHom (k : Type u) [Field k] : plane k ⟶ Spec (.of k) :=
  plane k ↘ Spec (.of k)

/-- The structure morphism of the affine plane is locally of finite type. -/
instance instLocallyOfFiniteType_planeHom (k : Type u) [Field k] :
    LocallyOfFiniteType (planeHom k) :=
  inferInstance

/-- The affine plane over a field is locally Noetherian. -/
instance instIsLocallyNoetherian_plane (k : Type u) [Field k] :
    IsLocallyNoetherian (plane k) :=
  LocallyOfFiniteType.isLocallyNoetherian (planeHom k)

/-- The fibre product `W = X ×_S X`. -/
abbrev square (k : Type u) [Field k] : Scheme.{u} :=
  pullback (planeHom k) (planeHom k)

/-- The first projection `W ⟶ X`. -/
abbrev fst (k : Type u) [Field k] : square k ⟶ plane k :=
  pullback.fst (planeHom k) (planeHom k)

/-- The second projection `W ⟶ X`. -/
abbrev snd (k : Type u) [Field k] : square k ⟶ plane k :=
  pullback.snd (planeHom k) (planeHom k)

/-- The structure morphism `W ⟶ Spec k`. -/
abbrev squareToBase (k : Type u) [Field k] : square k ⟶ Spec (.of k) :=
  snd k ≫ planeHom k

/-- The structure morphism of the affine square is locally of finite type. -/
instance instLocallyOfFiniteType_squareToBase (k : Type u) [Field k] :
    LocallyOfFiniteType (squareToBase k) :=
  inferInstance

/-- The affine square is locally Noetherian. -/
instance instIsLocallyNoetherian_square (k : Type u) [Field k] :
    IsLocallyNoetherian (square k) :=
  LocallyOfFiniteType.isLocallyNoetherian (squareToBase k)

/-- The involution `σ : W ⟶ W` swapping the two factors. -/
abbrev involution (k : Type u) [Field k] : square k ⟶ square k :=
  (pullbackSymmetry (planeHom k) (planeHom k)).hom

/-- The `u`-coordinate on the affine plane. -/
def planeCoordU (k : Type u) [Field k] : Γ(plane k, ⊤) :=
  AffineSpace.coord (Spec (.of k)) (ULift.up (0 : Fin 2))

/-- The `v`-coordinate on the affine plane. -/
def planeCoordV (k : Type u) [Field k] : Γ(plane k, ⊤) :=
  AffineSpace.coord (Spec (.of k)) (ULift.up (1 : Fin 2))

/-- The total space `X_W = W ×_S X`. -/
abbrev totalOnSquare (k : Type u) [Field k] : Scheme.{u} :=
  pullback (planeHom k) (squareToBase k)

/-- The structure morphism `X_W ⟶ W`. -/
abbrev totalOnSquareHom (k : Type u) [Field k] : totalOnSquare k ⟶ square k :=
  pullback.snd (planeHom k) (squareToBase k)

/-- The projection `X_W ⟶ W` is locally of finite type. -/
instance instLocallyOfFiniteType_totalOnSquareHom (k : Type u) [Field k] :
    LocallyOfFiniteType (totalOnSquareHom k) :=
  inferInstance

/-- The section of `X_W ⟶ W` induced by the first projection `W ⟶ X`. -/
def firstSection (k : Type u) [Field k] : square k ⟶ totalOnSquare k :=
  pullback.lift (fst k) (𝟙 (square k)) (by simpa only [Category.id_comp] using
    (pullback.condition (f := planeHom k) (g := planeHom k)))

/-- The section of `X_W ⟶ W` induced by the second projection `W ⟶ X`. -/
def secondSection (k : Type u) [Field k] : square k ⟶ totalOnSquare k :=
  pullback.lift (snd k) (𝟙 (square k)) (Category.id_comp (squareToBase k)).symm

/-- The first section is a section of `X_W ⟶ W`. -/
theorem firstSection_comp (k : Type u) [Field k] :
    firstSection k ≫ totalOnSquareHom k = 𝟙 (square k) :=
  by
  simp only [firstSection, totalOnSquareHom, pullback.lift_snd]

/-- The second section is a section of `X_W ⟶ W`. -/
theorem secondSection_comp (k : Type u) [Field k] :
    secondSection k ≫ totalOnSquareHom k = 𝟙 (square k) :=
  by
  simp only [secondSection, totalOnSquareHom, pullback.lift_snd]

/-- The point of the fibre of `X_W / W` over `w` selected by the first
projection. -/
def firstSectionFiberPoint (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiber w :=
  Scheme.Hom.Section.fiberPoint (totalOnSquareHom k) (firstSection k)
    (firstSection_comp k) w

/-- The point of the fibre of `X_W / W` over `w` selected by the second
projection. -/
def secondSectionFiberPoint (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiber w :=
  Scheme.Hom.Section.fiberPoint (totalOnSquareHom k) (secondSection k)
    (secondSection_comp k) w

private theorem section_fiberPoint_dimension {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (y : S) :
    f.fiberDimensionFunction y (Scheme.Hom.Section.fiberPoint f s hs y) = 0 := by
  let t : Spec (S.residueField y) ⟶ f.fiber y :=
    pullback.lift (S.fromSpecResidueField y ≫ s) (𝟙 _)
      (by simp [Category.assoc, hs])
  let q := f.fiberToSpecResidueField y
  let p : Spec (S.residueField y) := IsLocalRing.closedPoint (S.residueField y)
  have ht : t ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have heq : t p = Scheme.Hom.Section.fiberPoint f s hs y := by
    apply (f.fiberι y).isEmbedding.injective
    calc
      f.fiberι y (t p) = (S.fromSpecResidueField y ≫ s) p := by
        change (t ≫ f.fiberι y) p = _
        rw [show t ≫ f.fiberι y = S.fromSpecResidueField y ≫ s from
          pullback.lift_fst _ _ _]
      _ = s y := by simp
      _ = f.fiberι y (Scheme.Hom.Section.fiberPoint f s hs y) := by
        simp [Scheme.Hom.Section.fiberPoint]
  have hsurcomp : Function.Surjective ((t ≫ q).residueFieldMap p).hom := by
    rw [Scheme.Hom.residueFieldMap_congr ht p]
    exact (ConcreteCategory.bijective_of_isIso _).2
  have hsur : Function.Surjective (q.residueFieldMap (t p)).hom := by
    intro a
    obtain ⟨r, hr⟩ := hsurcomp ((t.residueFieldMap p).hom a)
    refine ⟨r, (t.residueFieldMap p).hom.injective ?_⟩
    rw [Scheme.residueFieldMap_comp] at hr
    exact hr
  haveI : Algebra.IsAlgebraic
      ((Spec (S.residueField y)).residueField (q (t p)))
      ((f.fiber y).residueField (t p)) := ⟨fun a ↦ by
    obtain ⟨r, hr⟩ := hsur a
    rw [← hr]
    exact isAlgebraic_algebraMap r⟩
  rw [← heq]
  simp [Scheme.Hom.fiberDimensionFunction, Scheme.Hom.relativeDimensionFunction,
    Scheme.Hom.residueFieldTranscendenceDegreeAt, trdeg_eq_zero]

/-- The first section point is 0-dimensional on the fibre. -/
theorem firstSectionFiberPoint_dimension (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiberDimensionFunction w (firstSectionFiberPoint k w) = 0 := by
  exact section_fiberPoint_dimension (totalOnSquareHom k) (firstSection k)
    (firstSection_comp k) w

/-- The second section point is 0-dimensional on the fibre. -/
theorem secondSectionFiberPoint_dimension (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiberDimensionFunction w (secondSectionFiberPoint k w) = 0 := by
  exact section_fiberPoint_dimension (totalOnSquareHom k) (secondSection k)
    (secondSection_comp k) w

/-- The canonical relative 0-cycle `α` on `X_W / W`, with `α_w = [x₁] + [x₂]`. -/
def canonicalPairCycle (k : Type u) [Field k] :
    (totalOnSquareHom k).FiberCycleFamily 0 :=
  fun w ↦
    CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
      (firstSectionFiberPoint k w) (firstSectionFiberPoint_dimension k w) +
    CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
      (secondSectionFiberPoint k w) (secondSectionFiberPoint_dimension k w)

/-- Evaluating the canonical cycle recovers the sum of the two section points. -/
theorem canonicalPairCycle_eval (k : Type u) [Field k] (w : square k) :
    canonicalPairCycle k w =
      CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
        (firstSectionFiberPoint k w) (firstSectionFiberPoint_dimension k w) +
      CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
        (secondSectionFiberPoint k w) (secondSectionFiberPoint_dimension k w) :=
  rfl

/-- The canonical pair cycle is a relative 0-cycle. -/
theorem canonicalPairCycle_isRelative (k : Type u) [Field k] :
    RelativeCycle.IsRelative (canonicalPairCycle k) :=
  sorry

/-- The canonical pair cycle is fibrewise effective. -/
theorem canonicalPairCycle_isEffective (k : Type u) [Field k] :
    RelativeCycle.IsEffective (canonicalPairCycle k) := by
  classical
  intro w
  change 0 ≤ CycleGroup.toAlgebraicCycle _ _ (canonicalPairCycle k w)
  intro x
  change 0 ≤
    Function.locallyFinsuppWithin.single (firstSectionFiberPoint k w) (1 : ℤ) x +
      Function.locallyFinsuppWithin.single (secondSectionFiberPoint k w) (1 : ℤ) x
  simp only [Function.locallyFinsuppWithin.single_apply]
  split_ifs <;> simp

/-- The polynomial ring `k[u₁, u₂, v₁, v₂]`. -/
abbrev coordRing (k : Type u) [CommRing k] : Type u :=
  MvPolynomial (ULift.{u} (Fin 4)) k

/-- The generator `u₁`. -/
def genU1 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (0 : Fin 4))

/-- The generator `u₂`. -/
def genU2 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (1 : Fin 4))

/-- The generator `v₁`. -/
def genV1 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (2 : Fin 4))

/-- The generator `v₂`. -/
def genV2 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (3 : Fin 4))

/-- The invariant subalgebra
`k[u₁+u₂, u₁u₂, v₁+v₂, v₁v₂, u₁v₁+u₂v₂] ⊂ k[u₁, u₂, v₁, v₂]`. -/
def invariantSubalgebra (k : Type u) [CommRing k] : Subalgebra k (coordRing k) :=
  Algebra.adjoin k
    {genU1 k + genU2 k, genU1 k * genU2 k, genV1 k + genV2 k, genV1 k * genV2 k,
      genU1 k * genV1 k + genU2 k * genV2 k}

/-- The five listed generators adjoin to the invariant subalgebra. -/
theorem invariantSubalgebra_adjoin (k : Type u) [CommRing k] :
    invariantSubalgebra k =
      Algebra.adjoin k
        {genU1 k + genU2 k, genU1 k * genU2 k, genV1 k + genV2 k,
          genV1 k * genV2 k, genU1 k * genV1 k + genU2 k * genV2 k} :=
  rfl

/-- The quotient scheme `Sym²_S(X)` as the spectrum of the invariant
subalgebra. -/
def symmetricSquare (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of (invariantSubalgebra k))

/-- The four coordinates on `W` as global sections, in the order
`u₁, u₂, v₁, v₂`. -/
def squareCoords (k : Type u) [Field k] (i : ULift.{u} (Fin 4)) :
    Γ(square k, ⊤) :=
  let n := i.down.val
  if n = 0 then (fst k).appTop (planeCoordU k)
  else if n = 1 then (snd k).appTop (planeCoordU k)
  else if n = 2 then (fst k).appTop (planeCoordV k)
  else (snd k).appTop (planeCoordV k)

/-- The comparison of `W` with affine 4-space over `Spec k`. -/
def squareToAffine4 (k : Type u) [Field k] :
    square k ⟶ 𝔸(ULift.{u} (Fin 4); Spec (.of k)) :=
  AffineSpace.homOfVector (squareToBase k) (squareCoords k)

/-- The comparison of `W` with `Spec(k[u₁, u₂, v₁, v₂])`. -/
def squareToSpecCoordRing (k : Type u) [Field k] :
    square k ⟶ Spec (.of (coordRing k)) :=
  squareToAffine4 k ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 4)) (.of k)).hom

/-- The quotient morphism `W ⟶ Sym²_S(X)` induced by the subalgebra
inclusion. -/
def toSymmetricSquare (k : Type u) [Field k] : square k ⟶ symmetricSquare k :=
  squareToSpecCoordRing k ≫
    Spec.map (CommRingCat.ofHom (algebraMap (invariantSubalgebra k) (coordRing k)))

/-- The structure morphism `Sym²_S(X) ⟶ Spec k`. -/
def symmetricSquareToBase (k : Type u) [Field k] :
    symmetricSquare k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (invariantSubalgebra k)))

private theorem toSymmetricSquare_comp_base (k : Type u) [Field k] :
    toSymmetricSquare k ≫ symmetricSquareToBase k = squareToBase k := by
  change (squareToSpecCoordRing k ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (invariantSubalgebra k) (coordRing k)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (invariantSubalgebra k))) = squareToBase k
  rw [Category.assoc, ← Spec.map_comp]
  change squareToSpecCoordRing k ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* coordRing k)) = squareToBase k
  rw [squareToSpecCoordRing, Category.assoc,
    ← AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin 4)) (.of k),
    Iso.hom_inv_id_assoc]
  exact AffineSpace.homOfVector_over _ _

private theorem finiteType_invariantSubalgebra (k : Type u) [CommRing k] :
    Algebra.FiniteType k (invariantSubalgebra k) := by
  apply Algebra.FiniteType.adjoin_of_finite
  simp

/-- The symmetric square is locally Noetherian. -/
instance instIsLocallyNoetherian_symmetricSquare (k : Type u) [Field k] :
    IsLocallyNoetherian (symmetricSquare k) := by
  letI := finiteType_invariantSubalgebra k
  letI := Algebra.FiniteType.isNoetherianRing k (invariantSubalgebra k)
  exact inferInstanceAs (IsLocallyNoetherian (Spec (.of (invariantSubalgebra k))))

/-- The structure morphism of the symmetric square is locally of finite type. -/
instance instLocallyOfFiniteType_symmetricSquareToBase (k : Type u) [Field k] :
    LocallyOfFiniteType (symmetricSquareToBase k) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr (finiteType_invariantSubalgebra k)

/-- The quotient morphism `W ⟶ Sym²_S(X)` is locally of finite type. -/
instance instLocallyOfFiniteType_toSymmetricSquare (k : Type u) [Field k] :
    LocallyOfFiniteType (toSymmetricSquare k) := by
  have : LocallyOfFiniteType (toSymmetricSquare k ≫ symmetricSquareToBase k) := by
    rw [toSymmetricSquare_comp_base]
    infer_instance
  exact locallyOfFiniteType_of_comp (toSymmetricSquare k) (symmetricSquareToBase k)

/-- The morphism `W ⟶ Sym²_S(X)` lies over `Spec k`. -/
theorem toSymmetricSquare_comp (k : Type u) [Field k] :
    toSymmetricSquare k ≫ symmetricSquareToBase k = squareToBase k := by
  exact toSymmetricSquare_comp_base k

/-- The closed subscheme `V = Spec(k[u₁², v₁²])`, the image of the diagonal in
`Sym²_S(X)` in characteristic 2. -/
def diagonalSubalgebra (k : Type u) [CommRing k] : Subalgebra k (coordRing k) :=
  Algebra.adjoin k {genU1 k ^ 2, genV1 k ^ 2}

/-- The image of the diagonal as an affine scheme. -/
def diagonalImage (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of (diagonalSubalgebra k))

/-- Substitution of the diagonal `u₂ = u₁`, `v₂ = v₁` on the coordinate ring. -/
def diagonalSubstitution (k : Type u) [CommRing k] : coordRing k →ₐ[k] coordRing k :=
  MvPolynomial.aeval fun i : ULift.{u} (Fin 4) =>
    if i.down.val ≤ 1 then genU1 k else genV1 k

/-- Diagonal substitution takes invariant polynomials into the subalgebra generated
by the squares of the two diagonal coordinates in characteristic two. -/
theorem invariantToDiagonal_mem (k : Type u) [Field k] [CharP k 2]
    (x : invariantSubalgebra k) :
    diagonalSubstitution k (x : coordRing k) ∈ diagonalSubalgebra k := by
  have h : invariantSubalgebra k ≤
      (diagonalSubalgebra k).comap (diagonalSubstitution k) := by
    apply Algebra.adjoin_le
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have htwo : (2 : coordRing k) = 0 := CharP.cast_eq_zero _ 2
    have hadd (z : coordRing k) : z + z = 0 := by
      rw [← two_mul, htwo, zero_mul]
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · change diagonalSubstitution k (genU1 k + genU2 k) ∈ diagonalSubalgebra k
      simpa [diagonalSubstitution, genU1, genU2, hadd] using
        (diagonalSubalgebra k).zero_mem
    · change diagonalSubstitution k (genU1 k * genU2 k) ∈ diagonalSubalgebra k
      simpa [diagonalSubstitution, diagonalSubalgebra, genU1, genU2, genV1, pow_two] using
        (Algebra.subset_adjoin (R := k)
          (by simp : genU1 k ^ 2 ∈ ({genU1 k ^ 2, genV1 k ^ 2} : Set (coordRing k))))
    · change diagonalSubstitution k (genV1 k + genV2 k) ∈ diagonalSubalgebra k
      simpa [diagonalSubstitution, genV1, genV2, hadd] using
        (diagonalSubalgebra k).zero_mem
    · change diagonalSubstitution k (genV1 k * genV2 k) ∈ diagonalSubalgebra k
      simpa [diagonalSubstitution, diagonalSubalgebra, genU1, genV1, genV2, pow_two] using
        (Algebra.subset_adjoin (R := k)
          (by simp : genV1 k ^ 2 ∈ ({genU1 k ^ 2, genV1 k ^ 2} : Set (coordRing k))))
    · change diagonalSubstitution k
          (genU1 k * genV1 k + genU2 k * genV2 k) ∈ diagonalSubalgebra k
      simpa [diagonalSubstitution, genU1, genU2, genV1, genV2, hadd] using
        (diagonalSubalgebra k).zero_mem
  exact h x.property

/-- Restriction of the invariant subalgebra along the diagonal substitution. -/
def invariantToDiagonal (k : Type u) [Field k] [CharP k 2] :
    invariantSubalgebra k →ₐ[k] diagonalSubalgebra k :=
  ((diagonalSubstitution k).comp (invariantSubalgebra k).val).codRestrict
    (diagonalSubalgebra k) (invariantToDiagonal_mem k)

/-- The closed immersion of the diagonal image into `Sym²_S(X)` in
characteristic 2. -/
def diagonalImageToSymmetricSquare (k : Type u) [Field k] [CharP k 2] :
    diagonalImage k ⟶ symmetricSquare k :=
  Spec.map (CommRingCat.ofHom (invariantToDiagonal k).toRingHom)

/-- The structure morphism of `W` is smooth. -/
instance instSmooth_squareToBase (k : Type u) [Field k] : Smooth (squareToBase k) :=
  by
  have : Smooth (planeHom k) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
      (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (.of k)).inv,
      AffineSpace.SpecIso_inv_over, HasRingHomProperty.Spec_iff (P := @Smooth)]
    change RingHom.Smooth (algebraMap k (MvPolynomial (ULift.{u} (Fin 2)) k))
    rw [RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  exact inferInstanceAs (Smooth (snd k ≫ planeHom k))

/-- The affine square is a normal scheme. -/
theorem isNormal_square (k : Type u) [Field k] : (square k).isNormal :=
  sorry

/-- The affine square is weakly normal. -/
instance instWeaklyNormal_square (k : Type u) [Field k] :
    Scheme.WeaklyNormal (square k) :=
  sorry

/-- The symmetric square is a normal scheme. -/
theorem isNormal_symmetricSquare (k : Type u) [Field k] :
    (symmetricSquare k).isNormal :=
  sorry

/-- The symmetric square of the affine plane over a field is weakly normal. -/
instance instWeaklyNormal_symmetricSquare (k : Type u) [Field k] :
    Scheme.WeaklyNormal (symmetricSquare k) := sorry

/-- The associator identifying the nested pullback of `X` along
`W ⟶ Sym²_S(X)` with `X_W`. -/
def descentIso (k : Type u) [Field k] :
    pullback (pullback.snd (planeHom k) (symmetricSquareToBase k))
        (toSymmetricSquare k) ≅ totalOnSquare k :=
  pullbackLeftPullbackSndIso (planeHom k) (symmetricSquareToBase k)
      (toSymmetricSquare k) ≪≫
    pullback.congrHom rfl (toSymmetricSquare_comp k)

/-- The associator `descentIso` is a morphism over `W`. -/
theorem descentIso_hom_over (k : Type u) [Field k] :
    (descentIso k).hom ≫ totalOnSquareHom k =
      pullback.snd (pullback.snd (planeHom k) (symmetricSquareToBase k))
        (toSymmetricSquare k) :=
  by
  change ((pullbackLeftPullbackSndIso (planeHom k) (symmetricSquareToBase k)
    (toSymmetricSquare k)).hom ≫
      (pullback.congrHom rfl (toSymmetricSquare_comp k)).hom) ≫
        pullback.snd (planeHom k) (squareToBase k) = _
  have h : (pullback.congrHom (f₁ := planeHom k) rfl (toSymmetricSquare_comp k)).hom ≫
      pullback.snd (planeHom k) (squareToBase k) =
        pullback.snd (planeHom k) (toSymmetricSquare k ≫ symmetricSquareToBase k) :=
    pullback.lift_snd _ _ _
  rw [Category.assoc, h]
  exact pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- Over a characteristic-two field, the canonical pair zero-cycle on the product of two
affine planes does not descend to an effective relative zero-cycle on the symmetric square. -/
theorem not_exists_descentCycle_of_char_two (k : Type u) [Field k] [CharP k 2] :
    ¬ ∃ β : RelativeCycle.effective
          (pullback.snd (planeHom k) (symmetricSquareToBase k)) 0,
        (RelativeCycle.effectiveMapOfIsoOver (descentIso k).hom
            (descentIso_hom_over k) 0
            (RelativeCycle.effectiveBaseChange
              (pullback.snd (planeHom k) (symmetricSquareToBase k))
              (toSymmetricSquare k) 0 β) :
            (totalOnSquareHom k).FiberCycleFamily 0) =
          canonicalPairCycle k :=
  sorry

/-- Over a characteristic-two field, the effective relative zero-cycle functor of the affine
plane is not representable on weakly normal finite type schemes. -/
theorem effectiveFunctorWeaklyNormal_not_isRepresentable (k : Type u) [Field k]
    [CharP k 2] :
    ¬ (RelativeCycle.effectiveFunctorWeaklyNormal (planeHom k) 0).IsRepresentable :=
  sorry

end AlgebraicGeometry.AffinePlaneDegreeTwo
