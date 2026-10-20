module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# First-quadrant restriction of cohomological spectral sequences

Pages supported in nonnegative bidegrees restrict to natural bidegrees, with explicit
zero-boundary maps in both directions on their homology short complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.CohomologicalSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The inclusion of first-quadrant bidegrees `ℕ × ℕ` into `ℤ × ℤ` is injective. -/
theorem spectralSequenceNatEmbedding_injective (r : ℤ) :
    Function.Injective (fun pq : ℕ × ℕ ↦ ((pq.1 : ℤ), (pq.2 : ℤ))) :=
  by
    intro a b h
    have h₁ := congrArg (fun x : ℤ × ℤ ↦ x.1) h
    have h₂ := congrArg (fun x : ℤ × ℤ ↦ x.2) h
    dsimp at h₁ h₂
    exact Prod.ext (Int.ofNat_inj.mp h₁) (Int.ofNat_inj.mp h₂)

/-- First-quadrant page shapes embed into unbounded cohomological page shapes. -/
theorem spectralSequenceNatEmbedding_rel_iff (r : ℤ) (a b : ℕ × ℕ) :
    (spectralSequenceNat ⟨r, 1 - r⟩).Rel a b ↔
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (a.1, a.2) (b.1, b.2) :=
  by
    change (_ ∧ _) ↔ (a.1 + r, a.2 + (1 - r)) = ((b.1 : ℤ), (b.2 : ℤ))
    constructor
    · rintro ⟨h₁, h₂⟩
      exact Prod.ext h₁ h₂
    · intro h
      exact ⟨congrArg (fun x : ℤ × ℤ ↦ x.1) h,
        congrArg (fun x : ℤ × ℤ ↦ x.2) h⟩

/-- The complex-shape embedding of a first-quadrant cohomological page into the unbounded
cohomological page of the same index. -/
noncomputable def spectralSequenceNatEmbedding (r : ℤ) :
    (spectralSequenceNat ⟨r, 1 - r⟩).Embedding
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)) :=
  Embedding.mk'
    (spectralSequenceNat ⟨r, 1 - r⟩)
    (up' (⟨r, 1 - r⟩ : ℤ × ℤ))
    (fun pq ↦ (pq.1, pq.2))
    (spectralSequenceNatEmbedding_injective r)
    (spectralSequenceNatEmbedding_rel_iff r)

/-- The first-quadrant page embedding preserves and reflects the differential relation. -/
instance spectralSequenceNatEmbedding_isRelIff (r : ℤ) :
    (spectralSequenceNatEmbedding r).IsRelIff :=
  by
    dsimp [spectralSequenceNatEmbedding]
    infer_instance

/-- Evaluation of the first-quadrant page embedding. -/
theorem spectralSequenceNatEmbedding_f (r : ℤ) (p q : ℕ) :
    (spectralSequenceNatEmbedding r).f (p, q) = ((p : ℤ), (q : ℤ)) :=
  rfl

/-- A page is supported in the first quadrant when every object with a negative
coordinate is zero. -/
def PageSupportedInFirstQuadrant (r : ℤ)
    (K : HomologicalComplex C (up' (⟨r, 1 - r⟩ : ℤ × ℤ))) : Prop :=
  ∀ pq : ℤ × ℤ, pq.1 < 0 ∨ pq.2 < 0 → IsZero (K.X pq)

variable (r : ℤ)
  (K : HomologicalComplex C (up' (⟨r, 1 - r⟩ : ℤ × ℤ)))
  (hK : PageSupportedInFirstQuadrant r K) (pq : ℕ × ℕ)

include hK in
/-- The boundary comparison commutes with the incoming differential. -/
theorem firstQuadrantShortMap_comm₁₂ :
    (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).prev pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (pq.1, pq.2)
    then eqToHom (congrArg K.X h) else 0) ≫ (K.sc ((pq.1 : ℤ), (pq.2 : ℤ))).f =
      ((K.restriction (spectralSequenceNatEmbedding r)).sc pq).f ≫ 𝟙 _ := sorry

include hK in
/-- The boundary comparison commutes with the outgoing differential. -/
theorem firstQuadrantShortMap_comm₂₃ :
    𝟙 _ ≫ (K.sc ((pq.1 : ℤ), (pq.2 : ℤ))).g =
      ((K.restriction (spectralSequenceNatEmbedding r)).sc pq).g ≫ (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).next pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (pq.1, pq.2)
    then eqToHom (congrArg K.X h) else 0) := sorry

/-- The comparison of homology short complexes, using zero maps at discarded boundaries. -/
def firstQuadrantShortMap :
    (K.restriction (spectralSequenceNatEmbedding r)).sc pq ⟶ K.sc ((pq.1 : ℤ), (pq.2 : ℤ)) where
  τ₁ := (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).prev pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (pq.1, pq.2)
    then eqToHom (congrArg K.X h) else 0)
  τ₂ := 𝟙 _
  τ₃ := (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).next pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (pq.1, pq.2)
    then eqToHom (congrArg K.X h) else 0)
  comm₁₂ := firstQuadrantShortMap_comm₁₂ r K hK pq
  comm₂₃ := firstQuadrantShortMap_comm₂₃ r K hK pq

include hK in
/-- The boundary comparison commutes with the incoming differential. -/
theorem firstQuadrantShortMapInv_comm₁₂ :
    (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).prev pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (pq.1, pq.2)
    then eqToHom (congrArg K.X h.symm) else 0) ≫ ((K.restriction (spectralSequenceNatEmbedding r)).sc pq).f =
      (K.sc ((pq.1 : ℤ), (pq.2 : ℤ))).f ≫ 𝟙 _ := sorry

include hK in
/-- The boundary comparison commutes with the outgoing differential. -/
theorem firstQuadrantShortMapInv_comm₂₃ :
    𝟙 _ ≫ ((K.restriction (spectralSequenceNatEmbedding r)).sc pq).g =
      (K.sc ((pq.1 : ℤ), (pq.2 : ℤ))).g ≫ (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).next pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (pq.1, pq.2)
    then eqToHom (congrArg K.X h.symm) else 0) := sorry

/-- The reverse comparison of homology short complexes, using zero maps at discarded boundaries. -/
def firstQuadrantShortMapInv :
    K.sc ((pq.1 : ℤ), (pq.2 : ℤ)) ⟶ (K.restriction (spectralSequenceNatEmbedding r)).sc pq where
  τ₁ := (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).prev pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (pq.1, pq.2)
    then eqToHom (congrArg K.X h.symm) else 0)
  τ₂ := 𝟙 _
  τ₃ := (if h : (spectralSequenceNatEmbedding r).f
      ((spectralSequenceNat ⟨r, 1 - r⟩).next pq) =
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (pq.1, pq.2)
    then eqToHom (congrArg K.X h.symm) else 0)
  comm₁₂ := firstQuadrantShortMapInv_comm₁₂ r K hK pq
  comm₂₃ := firstQuadrantShortMapInv_comm₂₃ r K hK pq

/-- The two boundary comparisons induce right inverse homology maps. -/
theorem firstQuadrantShortMap_homology_hom_inv_id :
    ShortComplex.homologyMap (firstQuadrantShortMap r K hK pq) ≫
      ShortComplex.homologyMap (firstQuadrantShortMapInv r K hK pq) = 𝟙 _ := sorry

/-- The two boundary comparisons induce left inverse homology maps. -/
theorem firstQuadrantShortMap_homology_inv_hom_id :
    ShortComplex.homologyMap (firstQuadrantShortMapInv r K hK pq) ≫
      ShortComplex.homologyMap (firstQuadrantShortMap r K hK pq) = 𝟙 _ := sorry

/-- The boundary comparison induces an isomorphism on homology. -/
instance firstQuadrantShortMap_homology_isIso :
    IsIso (ShortComplex.homologyMap (firstQuadrantShortMap r K hK pq)) :=
  ⟨⟨ShortComplex.homologyMap (firstQuadrantShortMapInv r K hK pq),
    firstQuadrantShortMap_homology_hom_inv_id r K hK pq,
    firstQuadrantShortMap_homology_inv_hom_id r K hK pq⟩⟩

/-- Restriction of a supported page preserves its homology, and hence identifies it
with the corresponding entry of the successor page. -/
def firstQuadrantSequence_pageHomologyIso
    (E : CohomologicalSpectralSequence C 1)
    (r r' : ℤ) (pq : ℕ × ℕ) (hrr' : r + 1 = r') (hr : 1 ≤ r)
    (hK : PageSupportedInFirstQuadrant r (E.page r hr)) :
    ((E.page r hr).restriction (spectralSequenceNatEmbedding r)).homology pq ≅
      ((E.page r' (by lia)).restriction (spectralSequenceNatEmbedding r')).X pq :=
  ( { hom := ShortComplex.homologyMap (firstQuadrantShortMap r (E.page r hr) hK pq)
      inv := ShortComplex.homologyMap (firstQuadrantShortMapInv r (E.page r hr) hK pq)
      hom_inv_id := firstQuadrantShortMap_homology_hom_inv_id r (E.page r hr) hK pq
      inv_hom_id := firstQuadrantShortMap_homology_inv_hom_id r (E.page r hr) hK pq } ) ≪≫
    E.iso r r' (pq.1, pq.2) hrr' hr

/-- Restrict an E1-starting integer spectral sequence supported in the first quadrant
to natural bidegrees. -/
def firstQuadrantSequence
    (E : CohomologicalSpectralSequence C 1)
    (hE : ∀ r (hr : 1 ≤ r), PageSupportedInFirstQuadrant r (E.page r hr)) :
    CohomologicalSpectralSequenceNat C 1 where
  page r hr := (E.page r hr).restriction (spectralSequenceNatEmbedding r)
  iso r r' pq hrr' hr :=
    firstQuadrantSequence_pageHomologyIso E r r' pq hrr' hr (hE r hr)

/-- The pages of the first-quadrant sequence are restrictions of the integer pages. -/
theorem firstQuadrantSequence_page
    (E : CohomologicalSpectralSequence C 1)
    (hE : ∀ r (hr : 1 ≤ r), PageSupportedInFirstQuadrant r (E.page r hr))
    (r : ℤ) (hr : 1 ≤ r) :
    (firstQuadrantSequence E hE).page r hr =
      (E.page r hr).restriction (spectralSequenceNatEmbedding r) := rfl

end CategoryTheory.CohomologicalSpectralSequence
