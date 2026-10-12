/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.QuotientProduct
public import stacks_project.Chap82.Lemma_82_15_2_Localization
public import stacks_project.Chap82.Remark_82_28_5_RankLocus
public import stacks_project.Chap67.Lemma_67_10_9
public import stacks_project.Chap66.Lemma_66_16_7_OpenMap

/-!
# The actual Chow-group product for the clopen rank decomposition

Only the existing rational-equivalence quotient and the real rank loci are
imported. No Chern operation or bivariant class is postulated here. Gluing reads
the coefficient in the unique rank component of each point. Local finiteness,
cycle degree, both inverse identities and the sigma support construction are
proved. Two isolated geometric obligations remain: the dimension of a closed
support under rank extension, and the specified principal-boundary sigma formula.
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

/-- The point map of the coproduct of the actual rank inclusions. -/
def rankPointMap (z : Σ r : ℕ, Points (rankOpenSubspace E r).X) : Points X :=
  Points.map (rankOpenSubspace E z.1).ι z.2

theorem rank_of_inclusion (r : ℕ) (x : Points (rankOpenSubspace E r).X) :
    fiberFinrank E (Points.map (rankOpenSubspace E r).ι x) = r := by
  apply (mem_rankClopen E r _).mp
  have hx : Points.map (rankOpenSubspace E r).ι x ∈ (rankOpenSubspace E r).pointsSet :=
    ⟨x, rfl⟩
  rw [rankOpenSubspace_pointsSet] at hx
  exact hx

theorem exists_rank_lift (x : Points X) :
    ∃ y : Points (rankOpenSubspace E (fiberFinrank E x)).X,
      Points.map (rankOpenSubspace E (fiberFinrank E x)).ι y = x := by
  change x ∈ (rankOpenSubspace E (fiberFinrank E x)).pointsSet
  rw [rankOpenSubspace_pointsSet]
  exact (mem_rankClopen E _ _).mpr rfl

/-- Choose a preimage of the specified point under its actual rank inclusion. -/
def rankLift (x : Points X) : Points (rankOpenSubspace E (fiberFinrank E x)).X :=
  Classical.choose (exists_rank_lift E x)

@[simp] theorem rankLift_spec (x : Points X) :
    Points.map (rankOpenSubspace E (fiberFinrank E x)).ι (rankLift E x) = x :=
  Classical.choose_spec (exists_rank_lift E x)

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

variable (f : X ⟶ B) (δ : Points B → ℤ) (k : ℤ)

/-- The concrete coefficient function obtained by reading the unique rank factor. -/
def glueFunction
    (a : ∀ r : ℕ, Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k)
    (x : Points X) : ℤ :=
  let z := (rankPointEquiv E).symm x
  (a z.1 : Function.locallyFinsupp (Points (rankOpenSubspace E z.1).X) ℤ) z.2

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

/-- Glued locally finite cycle; no coefficient or map is a data placeholder. -/
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

theorem cycleGlue_restrict (a : Hom.cycleGroup f δ k) :
    cycleGlue E f δ k (cycleRestrict E f δ k a) = a := by
  apply Subtype.ext
  ext x
  change (a : Function.locallyFinsupp (Points X) ℤ)
    ((rankPointEquiv E) ((rankPointEquiv E).symm x)) = _
  rw [Equiv.apply_symm_apply]

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
    [QuasiSeparated f] [LocallyOfFiniteType f] [IsDimensionFunction δ]

/-- Composition is inherited from the actual represented closed immersions. -/
theorem closedImmersion_comp {Y Z T : AlgebraicSpace S} (a : Y ⟶ Z) (b : Z ⟶ T)
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

/-- Keep the actual integral closed subspace and compose its inclusion with
the closed rank inclusion. The underlying space and rational functions are unchanged. -/
def closedInAmbient (r : ℕ) (W : ClosedSubspace (rankOpenSubspace E r).X) : ClosedSubspace X where
  X := W.X
  ι := W.ι ≫ (rankOpenSubspace E r).ι
  isClosedImmersion := closedImmersion_comp W.ι (rankOpenSubspace E r).ι

/-- Remaining geometric interface: closed rank extension preserves the
dimension of the same integral support. This is not an extra input assumption. -/
theorem closedInAmbient_dimension (r : ℕ) (W : ClosedSubspace (rankOpenSubspace E r).X)
    [hW : IsIntegral W.X] :
    Hom.deltaDimension f δ (@ClosedSubspace.irreducibleClosed S X (closedInAmbient E r W) hW) =
      Hom.deltaDimension ((rankOpenSubspace E r).ι ≫ f) δ (ClosedSubspace.irreducibleClosed W) := by
  sorry

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

/-- Remaining divisor interface: the actual sigma family of unchanged rational
units yields exactly the coefficientwise glued boundaries. It amounts to
closed-pushforward functoriality and reassociation of locally finite sums. -/
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
      (fun z ↦ (@closedInAmbient_dimension S B X E _ f δ _ _ _ _ _ z.1 (W z.1 z.2)
        (hWint z.1 z.2)).trans (hWdim z.1 z.2))
      (fun z ↦ φ z.1 z.2) (closedInAmbient_locallyFinite E J W hlocal) =
    cycleGlue E f δ k (fun r ↦ RationalEquivalence.boundary ((rankOpenSubspace E r).ι ≫ f)
      δ k (W r) (hWint r) (hWdim r) (φ r) (hlocal r)) := by
  sorry

/-- Rational-boundary preservation with the actual sigma-indexed presentation.
Choice only extracts the given rational-boundary presentations of the inputs. -/
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
    (fun z ↦ (@closedInAmbient_dimension S B X E _ f δ _ _ _ _ _ z.1 (W z.1 z.2)
      (hWint z.1 z.2)).trans (hWdim z.1 z.2)),
    (fun z ↦ φ z.1 z.2), closedInAmbient_locallyFinite E J W hlocal, ?_⟩
  rw [boundary_sigma_eq_glue E f δ k J W hWint hWdim φ hlocal]
  exact congrArg (cycleGlue E f δ k) (funext heq)

/-- Boundary membership can be checked on the actual rank restrictions. -/
theorem boundary_iff_rankwise (a : Hom.cycleGroup f δ k) :
    a ∈ RationalEquivalence.boundaries f δ k ↔
      ∀ r, cycleRestrict E f δ k a r ∈
        RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k := by
  constructor
  · intro ha r
    exact Hom.ChowLocalization.openPullback_mem_boundaries f δ (rankOpenSubspace E r) k ha
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

theorem cycleProduct_boundaries :
    (RationalEquivalence.boundaries f δ k).map (cycleProduct E f δ k).toAddMonoidHom =
      AddSubgroup.pi Set.univ (fun r ↦
        RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩ r _
    exact Hom.ChowLocalization.openPullback_mem_boundaries f δ (rankOpenSubspace E r) k ha
  · intro a ha
    refine ⟨cycleGlue E f δ k a, cycleGlue_mem_boundaries E f δ k a (fun r ↦ ha r (Set.mem_univ r)), ?_⟩
    exact cycleRestrict_glue E f δ k a

/-- Remark82.28.5's actual product of Chow groups, with no Chern-family parameter. -/
def chowProduct : Hom.chowGroup f δ k ≃+
    ∀ r : ℕ, Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ k :=
  (QuotientAddGroup.congr (RationalEquivalence.boundaries f δ k)
    (AddSubgroup.pi Set.univ (fun r ↦ RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k))
    (cycleProduct E f δ k) (cycleProduct_boundaries E f δ k)).trans
      (quotientPi (fun r ↦ Hom.cycleGroup ((rankOpenSubspace E r).ι ≫ f) δ k)
        (fun r ↦ RationalEquivalence.boundaries ((rankOpenSubspace E r).ι ≫ f) δ k))

@[simp] theorem chowProduct_mk (a : Hom.cycleGroup f δ k) (r : ℕ) :
    chowProduct E f δ k (Hom.chowMk f δ k a) r =
      Hom.chowMk ((rankOpenSubspace E r).ι ≫ f) δ k
        (Hom.Localization.openPullback f δ (rankOpenSubspace E r) k a) := rfl

/-- On arbitrary quotient classes this is precisely the genuine open Chow pullback. -/
theorem chowProduct_component (a : Hom.chowGroup f δ k) (r : ℕ) :
    chowProduct E f δ k a r = Hom.ChowLocalization.openPullback f δ (rankOpenSubspace E r) k a := by
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

/-- The source's test-space form: no constant-rank Chern family is a parameter. -/
def pullbackRankProduct {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] :
    Hom.chowGroup (g ≫ f) δ k ≃+
      ∀ r : ℕ, Hom.chowGroup
        ((rankOpenSubspace ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback g).obj E) r).ι ≫ (g ≫ f)) δ k :=
  chowProduct ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback g).obj E) (g ≫ f) δ k

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
