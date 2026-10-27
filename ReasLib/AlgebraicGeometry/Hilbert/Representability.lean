/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.Hilbert.Sheaf
public import ReasLib.AlgebraicGeometry.Hilbert.Limit
public import ReasLib.AlgebraicGeometry.Hilbert.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.FiniteSet
public import ReasLib.AlgebraicGeometry.Scheme.BigZariski.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/-- A finite family of points in one fiber of `X ⟶ S` is contained in an affine open of `X`. -/
class FiberPointsContainedInAffineOpen {S : Scheme.{u}} (X : Over S) (d : ℕ) : Prop where
  exists_affineOpen (s : S) (x : Fin d → X.left)
    (hx : ∀ i, X.hom.base (x i) = s) :
      ∃ U : X.left.affineOpens, ∀ i, x i ∈ (U : X.left.Opens)

/-- An affine scheme contains every finite family of its points in an affine open. -/
instance fiberPointsContainedInAffineOpen_of_isAffine {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [IsAffine X.left] : FiberPointsContainedInAffineOpen X d where
  exists_affineOpen _ _ _ := ⟨⟨⊤, isAffineOpen_top X.left⟩, fun _ ↦ trivial⟩

/-- For affine schemes `X ⟶ S` and a natural number `d`, the degree-`d` Hilbert
functor of `X` over `S` is representable. -/
@[instance]
theorem functor_isRepresentable_of_isAffine {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [IsAffine X.left] [IsAffine S] :
    (functor X d).IsRepresentable := sorry

/-- If every finite family of points in a fiber of `X ⟶ S` lies in an affine open of `X`,
then the degree-`d` Hilbert functor of `X` over `S` is representable. -/
@[instance]
theorem functor_isRepresentable_of_fiber_points_contained_in_affineOpen
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [FiberPointsContainedInAffineOpen X d] :
    (functor X d).IsRepresentable := sorry

/-- Prime avoidance gives a basic open around a finite family inside any open of a spectrum. -/
private theorem exists_basicOpen_containing_family
    {R : Type u} [CommRing R] {d : ℕ}
    (p : Fin d → PrimeSpectrum R) (U : TopologicalSpace.Opens (PrimeSpectrum R))
    (hp : ∀ i, p i ∈ U) :
    ∃ r : R, (∀ i, p i ∈ PrimeSpectrum.basicOpen r) ∧ PrimeSpectrum.basicOpen r ≤ U := by
  classical
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp U.isOpen.isClosed_compl
  have hnot : ¬(I : Set R) ⊆ ⋃ q ∈ Set.range (fun i ↦ (p i).asIdeal), (q : Set R) := by
    intro h
    have hprime : ∀ q ∈ Set.range (fun i ↦ (p i).asIdeal), q ≠ ⊤ → q ≠ ⊤ → q.IsPrime := by
      rintro q ⟨i, rfl⟩ _ _
      exact (p i).isPrime
    obtain ⟨q, ⟨i, rfl⟩, hq⟩ :=
      (Ideal.subset_union_prime_finite (Set.finite_range _) (f := id) ⊤ ⊤ hprime).mp h
    have hpi : p i ∈ (U : Set (PrimeSpectrum R))ᶜ := by
      rw [hI]
      exact hq
    exact hpi (hp i)
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hnot
  refine ⟨r, ?_, ?_⟩
  · intro i
    change r ∉ (p i).asIdeal
    intro hri
    exact hr (Set.mem_biUnion (Set.mem_range_self i) hri)
  · intro q hq
    by_contra hqU
    have hqI : I ≤ q.asIdeal := by
      apply (PrimeSpectrum.mem_zeroLocus q I).mp
      rw [← hI]
      exact hqU
    exact hq (hqI hrI)

/-- A quasi-affine scheme contains every finite family of points in an affine open. -/
@[instance]
theorem fiberPointsContainedInAffineOpen_of_isQuasiAffine
    {S : Scheme.{u}} (X : Over S) (d : ℕ) [X.left.IsQuasiAffine] :
    FiberPointsContainedInAffineOpen X d where
  exists_affineOpen _ x _ := by
    obtain ⟨r, hr, hU⟩ := exists_basicOpen_containing_family
      (fun i ↦ X.left.toSpecΓ (x i)) X.left.toSpecΓ.opensRange (fun i ↦ ⟨x i, rfl⟩)
    exact ⟨⟨X.left.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r,
      (IsAffineOpen.Spec_basicOpen r).preimage_of_isOpenImmersion X.left.toSpecΓ hU⟩, hr⟩

/-- Affine neighborhoods of a fiber can be found after restricting to a neighborhood of its
base point, then mapped back along the open immersion. -/
private theorem fiberPointsContainedInAffineOpen_of_baseOpen
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      FiberPointsContainedInAffineOpen (Over.mk (X.hom ∣_ U)) d) :
    FiberPointsContainedInAffineOpen X d where
  exists_affineOpen s x hx := by
    obtain ⟨U, hsU, hU⟩ := h s
    let y : Fin d → (X.hom ⁻¹ᵁ U).toScheme := fun i ↦
      ⟨x i, by
        change X.hom.base (x i) ∈ U
        rw [hx i]
        exact hsU⟩
    have hy : ∀ i, (X.hom ∣_ U).base (y i) = ⟨s, hsU⟩ := by
      intro i
      apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hx i
    obtain ⟨V, hV⟩ : ∃ V : (X.hom ⁻¹ᵁ U).toScheme.affineOpens,
        ∀ i, y i ∈ V.1 := hU.exists_affineOpen ⟨s, hsU⟩ y hy
    refine ⟨⟨(X.hom ⁻¹ᵁ U).ι ''ᵁ V.1,
      V.2.image_of_isOpenImmersion (X.hom ⁻¹ᵁ U).ι⟩, ?_⟩
    intro i
    exact ⟨y i, hV i, rfl⟩

private theorem fiberPointsContainedInAffineOpen_of_relativelyAmple
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    {L : X.left.Modules} (hL : RelativelyAmple X.hom L) :
    FiberPointsContainedInAffineOpen X d := by
  apply fiberPointsContainedInAffineOpen_of_baseOpen X d
  intro s
  obtain ⟨U, hU, hsU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  refine ⟨U, hsU, ⟨?_⟩⟩
  intro _ x _
  obtain ⟨V, hV⟩ := Scheme.exists_affineOpen_containing_finiteSet_of_hasAmpleInvertibleModule
    ⟨restrictToBasePreimage X.hom L U, hL.isAmpleOnAffinePreimage ⟨U, hU⟩⟩
    (Set.range x) (Set.finite_range x)
  exact ⟨V, fun i ↦ hV (Set.mem_range_self i)⟩

/-- An immersion into a relative projective spectrum has affine neighborhoods of finite
families in a fiber, using the supplied affine-local projective-spectrum models. -/
private theorem fiberPointsContainedInAffineOpen_of_immersion_to_relativeProj
    {S P : Scheme.{u}} (X : Over S) (d : ℕ) {π : P ⟶ S}
    (R : Scheme.Hom.RelativeProjPresentation π)
    (i : X.left ⟶ P) [IsImmersion i] (hi : i ≫ π = X.hom) :
    FiberPointsContainedInAffineOpen X d := by
  apply fiberPointsContainedInAffineOpen_of_baseOpen X d
  intro s
  let C := R.affineChart s
  let U : S.Opens := C.baseOpen.1
  have he : X.hom ⁻¹ᵁ U ≤ i ⁻¹ᵁ (π ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hi]
  let j := i.resLE (π ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U) he ≫ C.sourceIso.hom
  haveI : IsImmersion j := inferInstance
  letI := C.affineAlgebra.gradeSetLike
  letI := C.affineAlgebra.gradeAddSubgroupClass
  letI := C.affineAlgebra.grading_inst
  refine ⟨U, C.mem_baseOpen, ⟨?_⟩⟩
  intro _ x _
  obtain ⟨V, hV⟩ := @Scheme.exists_affineOpen_containing_finiteSet_of_isImmersion_to_Proj
    (X.hom ⁻¹ᵁ U).toScheme C.affineAlgebra.ring C.affineAlgebra.grade
    C.affineAlgebra.ring.commRing C.affineAlgebra.gradeSetLike
    C.affineAlgebra.gradeAddSubgroupClass C.affineAlgebra.grading
    C.affineAlgebra.grading_inst j ‹IsImmersion j› (Set.range x) (Set.finite_range x)
  exact ⟨V, fun k ↦ hV (Set.mem_range_self k)⟩

/-- A quasi-affine morphism has an affine open containing every finite family of points
in one fiber. -/
theorem fiberPointsContainedInAffineOpen_of_quasiAffineHom
    {S : Scheme.{u}} (X : Over S) (d : ℕ) (hf : QuasiAffineHom X.hom) :
    FiberPointsContainedInAffineOpen X d := by
  apply fiberPointsContainedInAffineOpen_of_baseOpen X d
  intro s
  obtain ⟨U, hU, hsU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  haveI : (Over.mk (X.hom ∣_ U)).left.IsQuasiAffine := hf ⟨U, hU⟩
  exact ⟨U, hsU, fiberPointsContainedInAffineOpen_of_isQuasiAffine
    (Over.mk (X.hom ∣_ U)) d⟩

/-- A quasi-projective morphism has an affine open containing every finite family of points
in one fiber. -/
@[instance]
theorem fiberPointsContainedInAffineOpen_of_quasiProjective
    {S : Scheme.{u}} (X : Over S) (d : ℕ) [QuasiProjective X.hom] :
    FiberPointsContainedInAffineOpen X d := by
  obtain ⟨L, hL⟩ := QuasiProjective.exists_relativelyAmple (f := X.hom)
  exact fiberPointsContainedInAffineOpen_of_relativelyAmple X d hL

/-- A locally projective morphism has an affine open containing every finite family of points
in one fiber. -/
@[instance]
theorem fiberPointsContainedInAffineOpen_of_locallyProjective
    {S : Scheme.{u}} (X : Over S) (d : ℕ) [LocallyProjective X.hom] :
    FiberPointsContainedInAffineOpen X d := by
  obtain ⟨𝒰, h𝒰⟩ := LocallyProjective.exists_cover (f := X.hom)
  apply fiberPointsContainedInAffineOpen_of_baseOpen X d
  intro s
  let U := (𝒰.f (𝒰.idx s)).opensRange
  obtain ⟨P, π, ℰ, _, _, hπ, i, hi⟩ := (h𝒰 (𝒰.idx s)).exists_presentation
  haveI : IsClosedImmersion i := hi.isClosedImmersion
  haveI : IsImmersion i := inferInstance
  exact ⟨U, 𝒰.covers s, @fiberPointsContainedInAffineOpen_of_immersion_to_relativeProj
    U.toScheme P (Over.mk (X.hom ∣_ U)) d π hπ.presentation i
    ‹IsImmersion i› hi.comp_eq⟩

/-- A scheme with an ample invertible module contains every finite family of points
in an affine open. -/
theorem fiberPointsContainedInAffineOpen_of_hasAmpleInvertibleModule
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hX : Scheme.Modules.HasAmpleInvertibleModule X.left) :
    FiberPointsContainedInAffineOpen X d where
  exists_affineOpen _ x _ := by
    obtain ⟨U, hU⟩ := Scheme.exists_affineOpen_containing_finiteSet_of_hasAmpleInvertibleModule
      hX (Set.range x) (Set.finite_range x)
    exact ⟨U, fun i ↦ hU (Set.mem_range_self i)⟩

/-- If a morphism admits a relatively ample module, every finite family of points
in one fiber is contained in an affine open of its source. -/
theorem fiberPointsContainedInAffineOpen_of_exists_relativelyAmple
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hL : ∃ L : X.left.Modules, RelativelyAmple X.hom L) :
    FiberPointsContainedInAffineOpen X d := by
  obtain ⟨L, hL⟩ := hL
  exact fiberPointsContainedInAffineOpen_of_relativelyAmple X d hL

/-- If a morphism admits a relatively very ample module, every finite family of points
in one fiber is contained in an affine open of its source. -/
theorem fiberPointsContainedInAffineOpen_of_exists_relativelyVeryAmple
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hL : ∃ L : X.left.Modules, RelativelyVeryAmple X.hom L) :
    FiberPointsContainedInAffineOpen X d := by
  obtain ⟨L, hL⟩ := hL
  obtain ⟨P, π, ℰ, _, hπ, i, hi⟩ := hL.exists_presentation
  haveI : IsImmersion i := hi.isImmersion
  exact fiberPointsContainedInAffineOpen_of_immersion_to_relativeProj X d
    hπ.presentation i hi.comp_eq

end AlgebraicGeometry.Hilbert
