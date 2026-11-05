/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.QuotientProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Localization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RankLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Openness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition

/-!
# Chow groups of clopen rank decompositions

Restriction to the clopen rank loci identifies cycles and Chow groups with
the products of their rank components. Gluing reads the coefficient in the
unique rank component of each point. Rational boundaries restrict to rank
loci and glue along locally finite families of integral closed supports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open Function Set TopologicalSpace

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]

/-- The point map from the disjoint union of the rank loci to the ambient space. -/
def rankPointMap (z : Σ r : ℕ, Points (rankOpenSubspace E r).X) : Points X :=
  Points.map (rankOpenSubspace E z.1).ι z.2

/-- A point in the rank-`r` locus has ambient fiber rank `r`. -/
theorem rank_of_inclusion (r : ℕ) (x : Points (rankOpenSubspace E r).X) :
    fiberFinrank E (Points.map (rankOpenSubspace E r).ι x) = r := by
  apply (mem_rankClopen E r _).mp
  have hx : Points.map (rankOpenSubspace E r).ι x ∈ (rankOpenSubspace E r).pointsSet :=
    ⟨x, rfl⟩
  rw [rankOpenSubspace_pointsSet] at hx
  exact hx

/-- The field-valued representative of a point is a section of its actual rank open.
Every point of its source field spectrum has the same image in the ambient space. -/
theorem rankLift_mem (x : Points X) :
    (Quotient.out x).elem ∈
      (OpenSubspace.Construction.subfunctor X
        (rankClopen E (fiberFinrank E x)).toOpens).obj
          (Opposite.op (Quotient.out x).overObj) := by
  let p := Quotient.out x
  change Set.range (Points.map (X := ofOver p.overObj) (Y := X) (yonedaEquiv.symm p.elem)) ⊆
    {z | fiberFinrank E z = fiberFinrank E x}
  rw [show yonedaEquiv.symm p.elem = p.hom from yonedaEquiv.symm_apply_apply p.hom]
  rintro _ ⟨q, rfl⟩
  have hmap : Points.map p.hom q = x := by
    induction q using Quotient.inductionOn with
    | h q =>
      change Points.mk (q.map p.hom) = x
      have hqp : Points.mk (q.map p.hom) = Points.mk p := by
        apply Quotient.sound
        refine ⟨⟨q.map p.hom, FieldValuedPoint.Factorization.refl _, ?_⟩⟩
        let a : q.overObj ⟶ p.overObj := Yoneda.fullyFaithful.preimage q.hom
        refine ⟨a.left, Over.w a, ?_⟩
        change yoneda.map (Over.homMk a.left (Over.w a)) ≫ p.hom = q.hom ≫ p.hom
        have ha : Over.homMk a.left (Over.w a) = a := by ext; rfl
        rw [ha]
        exact congrArg (fun b : yoneda.obj q.overObj ⟶ yoneda.obj p.overObj ↦
          b ≫ (p.hom : yoneda.obj p.overObj ⟶ X.functorOfPoints))
            (Yoneda.fullyFaithful.map_preimage q.hom)
      exact hqp.trans (Quotient.out_eq x)
  change fiberFinrank E (Points.map p.hom q) = fiberFinrank E x
  rw [hmap]

/-- Lift the same field-valued representative by inserting its section into the
rank-open subfunctor; no preimage is selected from an admitted existence theorem. -/
def rankLift (x : Points X) : Points (rankOpenSubspace E (fiberFinrank E x)).X :=
  let p := Quotient.out x
  Points.mk (FieldValuedPoint.of p.K p.structureHom
    (yonedaEquiv.symm (⟨p.elem, rankLift_mem E x⟩ :
      (rankOpenSubspace E (fiberFinrank E x)).X.functorOfPoints.obj (Opposite.op p.overObj))))

/-- The lift to the point's rank locus maps back to that point. -/
@[simp] theorem rankLift_spec (x : Points X) :
    Points.map (rankOpenSubspace E (fiberFinrank E x)).ι (rankLift E x) = x := by
  let p := Quotient.out x
  have hhom :
      yonedaEquiv.symm (⟨p.elem, rankLift_mem E x⟩ :
      (rankOpenSubspace E (fiberFinrank E x)).X.functorOfPoints.obj (Opposite.op p.overObj)) ≫
        (rankOpenSubspace E (fiberFinrank E x)).ι = p.hom := by
    change yonedaEquiv.symm p.elem = p.hom
    exact yonedaEquiv.symm_apply_apply p.hom
  change Points.mk (FieldValuedPoint.of p.K p.structureHom
    (yonedaEquiv.symm (⟨p.elem, rankLift_mem E x⟩ :
      (rankOpenSubspace E (fiberFinrank E x)).X.functorOfPoints.obj (Opposite.op p.overObj)) ≫
      (rankOpenSubspace E (fiberFinrank E x)).ι)) = x
  exact (congrArg (fun h : ofOver p.overObj ⟶ X ↦
    Points.mk (FieldValuedPoint.of p.K p.structureHom h)) hhom).trans (Quotient.out_eq x)

/-- Every point lifts to the rank locus indexed by its fiber rank. -/
theorem exists_rank_lift (x : Points X) :
    ∃ y : Points (rankOpenSubspace E (fiberFinrank E x)).X,
      Points.map (rankOpenSubspace E (fiberFinrank E x)).ι y = x :=
  ⟨rankLift E x, rankLift_spec E x⟩

/-- The point map from the disjoint union of the rank loci is injective. -/
theorem rankPointMap_injective : Function.Injective (rankPointMap E) := by
  rintro ⟨r, x⟩ ⟨s, y⟩ h
  have hrs : r = s := by
    calc
      r = fiberFinrank E (rankPointMap E ⟨r, x⟩) := (rank_of_inclusion E r x).symm
      _ = fiberFinrank E (rankPointMap E ⟨s, y⟩) := congrArg (fiberFinrank E) h
      _ = s := rank_of_inclusion E s y
  subst s
  -- This instance is the genuine monomorphism of the open-subspace inclusion.
  -- Local instance justification (defeq pin): Cancellation uses the monomorphism proof belonging to this rank open inclusion, whose point map occurs in the displayed equality.
  letI : Mono (rankOpenSubspace E r).ι := (OpenSubspace.spec _).2
  have hxy : x = y := Points.map_injective_of_mono _ h
  cases hxy
  rfl

/-- The inverse records the actual fibre rank and lifts the same point. -/
def rankPointEquiv : (Σ r : ℕ, Points (rankOpenSubspace E r).X) ≃ Points X where
  toFun := rankPointMap E
  invFun x := ⟨fiberFinrank E x, rankLift E x⟩
  left_inv z := rankPointMap_injective E (rankLift_spec E (rankPointMap E z))
  right_inv := rankLift_spec E

variable (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)

/-- The concrete coefficient function obtained by reading the unique rank factor. -/
def glueFunction
    (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k)
    (x : Points X) : ℤ :=
  let z := (rankPointEquiv E).symm x
  (a z.1 : Function.locallyFinsupp (Points (rankOpenSubspace E z.1).X) ℤ) z.2

/-- The glued coefficient function restricts to the supplied coefficient on each rank locus. -/
@[simp] theorem glueFunction_on_rank
    (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k)
    (r : ℕ) (x : Points (rankOpenSubspace E r).X) :
    glueFunction E f δ k a (Points.map (rankOpenSubspace E r).ι x) =
      (a r : Function.locallyFinsupp (Points (rankOpenSubspace E r).X) ℤ) x := by
  change (fun z : Σ r : ℕ, Points (rankOpenSubspace E r).X ↦
    (a z.1 : Function.locallyFinsupp (Points (rankOpenSubspace E z.1).X) ℤ) z.2)
      ((rankPointEquiv E).symm ((rankPointEquiv E) ⟨r, x⟩)) = _
  rw [Equiv.symm_apply_apply]

/-- A neighbourhood inside the point's open rank locus meets only that component,
where the supplied cycle has locally finite support. -/
theorem glueFunction_locallyFinite
    (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k) :
    LocallyFiniteSupport (glueFunction E f δ k a) := by
  intro x
  let r := fiberFinrank E x
  let y := rankLift E x
  obtain ⟨t, ht, hfinite⟩ := (a r).1.supportLocallyFiniteWithinDomain' y (Set.mem_univ y)
  refine ⟨Points.map (rankOpenSubspace E r).ι '' t, ?_, ?_⟩
  · have hopen := (AlgebraicGeometry.AlgebraicSpace.Etale.isOpenMap
      (rankOpenSubspace E r).ι).image_mem_nhds ht
    simpa only [r, y, rankLift_spec] using hopen
  · apply (hfinite.image (Points.map (rankOpenSubspace E r).ι)).subset
    rintro z ⟨⟨w, hw, rfl⟩, hz⟩
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    change (a r).val.toFun w ≠ 0
    change glueFunction E f δ k a (Points.map (rankOpenSubspace E r).ι w) ≠ 0 at hz
    rw [glueFunction_on_rank] at hz
    exact hz

/-- The locally finitely supported coefficient function obtained by gluing rank-locus cycles. -/
def glueRaw (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := glueFunction E f δ k a
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := glueFunction_locallyFinite E f δ k a x

/-- A singleton cycle and genuine open restriction detect equality of relative
degrees, so every glued nonzero coefficient still has degree k. -/
theorem glueRaw_mem (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k) :
    glueRaw E f δ k a ∈ Hom.cycleGroup f δ k := by
  classical
  intro x hx
  let z := (rankPointEquiv E).symm x
  have hz : Points.map (rankOpenSubspace E z.1).ι z.2 = x :=
    (rankPointEquiv E).apply_symm_apply x
  -- A genuine singleton cycle at x detects preservation of degree by the
  -- existing open restriction; no guessed residue-field equality is introduced.
  let single : Hom.cycleGroup f δ (Hom.relativeDimensionFunction f δ x) :=
    ⟨Function.locallyFinsuppWithin.single x 1, by
      intro w hw
      by_cases h : w = x
      · simpa only [h]
      · simp [Function.locallyFinsuppWithin.single_apply, h] at hw⟩
  have hdim := (Hom.Localization.openPullback f δ (rankOpenSubspace E z.1)
    (Hom.relativeDimensionFunction f δ x) single).property z.2
  have hone : (Hom.Localization.openPullback f δ (rankOpenSubspace E z.1)
      (Hom.relativeDimensionFunction f δ x) single).val z.2 ≠ 0 := by
    change Function.locallyFinsuppWithin.single x (1 : ℤ)
      (Points.map (rankOpenSubspace E z.1).ι z.2) ≠ 0
    simp [hz]
  have hdegree := (a z.1).property z.2 hx
  exact (hdim hone).symm.trans hdegree

/-- The explicit gluing homomorphism on genuine dimension-supported cycles. -/
def cycleGlue :
    (∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k) →+
      Hom.cycleGroup f δ k where
  toFun a := ⟨glueRaw E f δ k a, glueRaw_mem E f δ k a⟩
  map_zero' := by apply Subtype.ext; ext x; rfl
  map_add' a b := by apply Subtype.ext; ext x; rfl

/-- The existing coefficientwise open restriction, taken in every rank. -/
def cycleRestrict : Hom.cycleGroup f δ k →+
    ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k :=
  AddMonoidHom.pi fun r ↦ Hom.Localization.openPullback f δ (rankOpenSubspace E r) k

/-- Gluing all rank restrictions recovers the original cycle. -/
theorem cycleGlue_restrict (a : Hom.cycleGroup f δ k) :
    cycleGlue E f δ k (cycleRestrict E f δ k a) = a := by
  apply Subtype.ext
  ext x
  change (a : Function.locallyFinsupp (Points X) ℤ)
    ((rankPointEquiv E) ((rankPointEquiv E).symm x)) = _
  rw [Equiv.apply_symm_apply]

/-- Restricting a glued cycle recovers each of its rank components. -/
theorem cycleRestrict_glue
    (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k) :
    cycleRestrict E f δ k (cycleGlue E f δ k a) = a := by
  funext r
  apply Subtype.ext
  ext x
  exact glueFunction_on_rank E f δ k a r x

/-- The cycle equivalence has the specified restriction and gluing as its data. -/
def cycleProduct : Hom.cycleGroup f δ k ≃+
    ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k where
  toFun := cycleRestrict E f δ k
  invFun := cycleGlue E f δ k
  left_inv := cycleGlue_restrict E f δ k
  right_inv := cycleRestrict_glue E f δ k
  map_add' := (cycleRestrict E f δ k).map_add

variable [UniversallyCatenary B] [IsQuasiSeparated B]
    [QuasiSeparated f] [IsDimensionFunction δ]

/-- The composition of two closed immersions of algebraic spaces is a closed immersion. -/
private theorem closedImmersion_comp {Y Z T : AlgebraicSpace S} (a : Y ⟶ Z) (b : Z ⟶ T)
    [IsClosedImmersion a] [IsClosedImmersion b] : IsClosedImmersion (a ≫ b) := by
  -- Local instance justification (proof-local temporary data): Lift composition of closed immersions from schemes to the over category before applying the represented-presheaf composition theorem.
  letI : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}) :
        MorphismProperty (Over S)) :=
    ⟨fun a b ha hb ↦
      (inferInstance : MorphismProperty.IsMultiplicative
        (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).comp_mem a.left b.left ha hb⟩
  -- Local instance justification (proof-local temporary data): This instance transports the preceding over-category closed-immersion composition law through Yoneda for these inclusions.
  letI := MorphismProperty.relative_isStableUnderComposition
    (P := (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}) :
      MorphismProperty (Over S))) (F := yoneda)
  exact ⟨MorphismProperty.comp_mem
    ((MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf)
    a b (IsClosedImmersion.presheaf (f := a)) (IsClosedImmersion.presheaf (f := b))⟩

/-- A closed subspace of a clopen rank locus is a closed subspace of the ambient space,
with the same underlying algebraic space and the composite inclusion. -/
def closedInAmbient (r : ℕ) (W : ClosedSubspace (rankOpenSubspace E r).X) : ClosedSubspace X where
  X := W.X
  ι := W.ι ≫ (rankOpenSubspace E r).ι
  isClosedImmersion := by
    exact @closedImmersion_comp S W.X (rankOpenSubspace E r).X X
      W.ι (rankOpenSubspace E r).ι W.isClosedImmersion inferInstance

/-- Extending an integral closed subspace along a clopen rank inclusion preserves
its dimension relative to the base dimension function. -/
theorem closedInAmbient_dimension (r : ℕ) (W : ClosedSubspace (rankOpenSubspace E r).X)
    [hW : IsIntegral W.X] :
    Hom.deltaDimension f δ (@ClosedSubspace.irreducibleClosed S X (closedInAmbient E r W) hW) =
      Hom.deltaDimension ((rankOpenSubspace E r).ι ≫ f) δ (ClosedSubspace.irreducibleClosed W) := sorry

/-- The sigma family is locally finite: near a point only its own rank can
occur, and there the original integral-support family is locally finite. -/
theorem closedInAmbient_locallyFinite
    (J : ℕ → Type (u + 1)) (W : ∀ r, J r → ClosedSubspace (rankOpenSubspace E r).X)
    (hlocal : ∀ r, LocallyFinite fun j ↦ (W r j).pointsSet) :
    LocallyFinite fun z : Σ r, J r ↦ (closedInAmbient E z.1 (W z.1 z.2)).pointsSet := by
  intro x
  let r := fiberFinrank E x
  let y := rankLift E x
  obtain ⟨t, ht, hfinite⟩ := hlocal r y
  refine ⟨Points.map (rankOpenSubspace E r).ι '' t, ?_, ?_⟩
  · have hopen := (AlgebraicGeometry.AlgebraicSpace.Etale.isOpenMap
      (rankOpenSubspace E r).ι).image_mem_nhds ht
    simpa only [r, y, rankLift_spec] using hopen
  · apply (hfinite.image (fun j ↦ (⟨r, j⟩ : Σ r, J r))).subset
    rintro ⟨s, j⟩ ⟨z, ⟨w, hw⟩, ⟨v, hv, hz⟩⟩
    have hw' : Points.map (rankOpenSubspace E s).ι (Points.map (W s j).ι w) = z := by
      simpa only [closedInAmbient, Points.map_comp] using hw
    have hsr : s = r := by
      calc
        s = fiberFinrank E z := by rw [← hw']; exact (rank_of_inclusion E s _).symm
        _ = r := by rw [← hz]; exact rank_of_inclusion E r v
    subst s
    refine ⟨j, ?_, rfl⟩
    have hpoints : Points.map (W r j).ι w = v :=
      Points.map_injective_of_mono (rankOpenSubspace E r).ι (hw'.trans hz.symm)
    exact ⟨v, ⟨w, hpoints⟩, hv⟩

/-- The rational boundary of a locally finite family of integral closed supports
across rank loci is the gluing of the boundaries on those loci. -/
theorem boundary_sigma_eq_glue
    (J : ℕ → Type (u + 1)) (W : ∀ r, J r → ClosedSubspace (rankOpenSubspace E r).X)
    (hWint : ∀ r j, IsIntegral (W r j).X)
    (hWdim : ∀ r j, Hom.deltaDimension ((rankOpenSubspace E r).ι ≫ f) δ
      (@ClosedSubspace.irreducibleClosed S _ (W r j) (hWint r j)) = k + 1)
    (φ : ∀ r j, (RationalFunction (W r j).X)ˣ)
    (hlocal : ∀ r, LocallyFinite fun j ↦ (W r j).pointsSet) :
    RationalEquivalence.boundary f δ k
      (fun z : Σ r, J r ↦ closedInAmbient E z.1 (W z.1 z.2))
      (fun z ↦ hWint z.1 z.2)
      (fun z ↦ (@closedInAmbient_dimension S B X E _ f _ δ _ _ _ _ z.1 (W z.1 z.2)
        (hWint z.1 z.2)).trans (hWdim z.1 z.2))
      (fun z ↦ φ z.1 z.2) (closedInAmbient_locallyFinite E J W hlocal) =
    cycleGlue E f δ k (fun r ↦ RationalEquivalence.boundary ((rankOpenSubspace E r).ι ≫ f)
      δ k (W r) (hWint r) (hWdim r) (φ r) (hlocal r)) := sorry

/-- Gluing rational boundaries on all rank loci gives a rational boundary on the ambient space. -/
theorem cycleGlue_mem_boundaries
    (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k)
    (ha : ∀ r, a r ∈ RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k) :
    cycleGlue E f δ k a ∈ RationalEquivalence.boundaries f δ k := by
  have witnesses : ∀ r, RationalEquivalence.IsRationallyTrivial
      ((rankOpenSubspace E r).ι ≫ f) δ k (a r) := ha
  choose J W hWint hWdim φ hlocal heq using witnesses
  change RationalEquivalence.IsRationallyTrivial f δ k (cycleGlue E f δ k a)
  refine ⟨(Σ r, J r), (fun z ↦ closedInAmbient E z.1 (W z.1 z.2)),
    (fun z ↦ hWint z.1 z.2),
    (fun z ↦ (@closedInAmbient_dimension S B X E _ f _ δ _ _ _ _ z.1 (W z.1 z.2)
      (hWint z.1 z.2)).trans (hWdim z.1 z.2)),
    (fun z ↦ φ z.1 z.2), closedInAmbient_locallyFinite E J W hlocal, ?_⟩
  rw [boundary_sigma_eq_glue E f δ k J W hWint hWdim φ hlocal]
  exact congrArg (cycleGlue E f δ k) (funext heq)

/-- Restriction to a clopen rank locus carries rational boundaries to rational boundaries. -/
theorem rankOpenPullback_mem_boundaries (r : ℕ) :
    RationalEquivalence.boundaries f δ k ≤
      (RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k).comap
        (Hom.Localization.openPullback f δ (rankOpenSubspace E r) k) :=
  sorry

/-- Restriction of Chow classes to a clopen rank locus, induced by cycle restriction. -/
def rankChowRestrict (r : ℕ) :
    Hom.chowGroup f δ k →+ Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries f δ k)
    (RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k)
    (Hom.Localization.openPullback f δ (rankOpenSubspace E r) k)
    (rankOpenPullback_mem_boundaries E f δ k r)

/-- Restricting the class of a cycle to a rank locus gives the class of its cycle restriction. -/
@[simp] theorem rankChowRestrict_chowMk (r : ℕ) (a : Hom.cycleGroup f δ k) :
    rankChowRestrict E f δ k r (Hom.chowMk f δ k a) =
      Hom.chowMk ((rankOpenSubspace E r).ι ≫ f) δ k
        (Hom.Localization.openPullback f δ (rankOpenSubspace E r) k a) := rfl

/-- Boundary membership can be checked on the rank restrictions. -/
theorem boundary_iff_rankwise (a : Hom.cycleGroup f δ k) :
    a ∈ RationalEquivalence.boundaries f δ k ↔
      ∀ r, cycleRestrict E f δ k a r ∈
        RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k := by
  constructor
  · intro ha r
    exact rankOpenPullback_mem_boundaries E f δ k r ha
  · intro ha
    have h := cycleGlue_mem_boundaries E f δ k (cycleRestrict E f δ k a) ha
    simpa only [cycleGlue_restrict] using h

/-- Rational equivalence is preserved and reflected by the concrete restrictions. -/
theorem rationalEquivalence_iff_rankwise (a b : Hom.cycleGroup f δ k) :
    RationalEquivalence.RationallyEquivalent f δ k a b ↔
      ∀ r, RationalEquivalence.RationallyEquivalent ((rankOpenSubspace E r).ι ≫ f) δ k
        (cycleRestrict E f δ k a r) (cycleRestrict E f δ k b r) := by
  simpa only [RationalEquivalence.RationallyEquivalent, map_sub, Pi.sub_apply] using
    boundary_iff_rankwise E f δ k (a - b)

/-- The cycle product equivalence identifies ambient rational boundaries with
the product of the rational-boundary subgroups of the rank loci. -/
theorem cycleProduct_boundaries :
    (RationalEquivalence.boundaries f δ k).map (cycleProduct E f δ k).toAddMonoidHom =
      AddSubgroup.pi Set.univ (fun r ↦
        RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩ r _
    exact rankOpenPullback_mem_boundaries E f δ k r ha
  · intro a ha
    refine ⟨cycleGlue E f δ k a, cycleGlue_mem_boundaries E f δ k a (fun r ↦ ha r (Set.mem_univ r)), ?_⟩
    exact cycleRestrict_glue E f δ k a

/-- The Chow group is additively equivalent to the full product of the Chow groups of the rank loci. -/
def chowProduct : Hom.chowGroup f δ k ≃+
    ∀ r : ℕ, Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ k :=
  (QuotientAddGroup.congr (RationalEquivalence.boundaries f δ k)
    (AddSubgroup.pi Set.univ (fun r ↦ RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k))
    (cycleProduct E f δ k) (cycleProduct_boundaries E f δ k)).trans
      (quotientPi (fun r ↦ Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k)
        (fun r ↦ RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k))

/-- The rank component of a cycle's Chow class is the Chow class of its open restriction. -/
@[simp] theorem chowProduct_mk (a : Hom.cycleGroup f δ k) (r : ℕ) :
    chowProduct E f δ k (Hom.chowMk f δ k a) r =
      Hom.chowMk ((rankOpenSubspace E r).ι ≫ f) δ k
        (Hom.Localization.openPullback f δ (rankOpenSubspace E r) k a) := rfl

/-- Each component of the Chow product equivalence is restriction to that rank locus. -/
theorem chowProduct_component (a : Hom.chowGroup f δ k) (r : ℕ) :
    chowProduct E f δ k a r = rankChowRestrict E f δ k r a := by
  induction a using Quotient.inductionOn with
  | h a => rfl

/-- Gluing representatives then taking their true rational-equivalence class
is the inverse product map, independent of the chosen representatives. -/
theorem chowProduct_symm_mk
    (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k) :
    (chowProduct E f δ k).symm (fun r ↦ Hom.chowMk ((rankOpenSubspace E r).ι ≫ f) δ k (a r)) =
      Hom.chowMk f δ k (cycleGlue E f δ k a) := by
  apply (chowProduct E f δ k).injective
  rw [AddEquiv.apply_symm_apply]
  funext r
  rw [chowProduct_mk]
  exact congrArg (Hom.chowMk ((rankOpenSubspace E r).ι ≫ f) δ k)
    (congrFun (cycleRestrict_glue E f δ k a) r).symm

/-- On a good test space, the Chow group is the product of the Chow groups of
the rank loci of the pulled-back module. -/
def pullbackRankProduct {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] :
    Hom.chowGroup (g ≫ f) δ k ≃+
      ∀ r : ℕ, Hom.chowGroup
        ((rankOpenSubspace ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback g).obj E) r).ι ≫ (g ≫ f)) δ k :=
  chowProduct ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback g).obj E) (g ≫ f) δ k

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
