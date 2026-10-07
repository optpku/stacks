module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration
public import stacks_project.Chap69.Lemma_69_6_3_Comparison

/-!
# First filtration of the alternating Čech Hom bicomplex

The first filtration of `Hom(K^p, I^q)` is the source of the Ext spectral sequence
converging to étale cohomology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open HomologicalComplex HomologicalComplex₂ Opposite ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Chosen cohomological spectral sequence associated to the first filtration of
`Hom(K^•, I^•)`. -/
noncomputable def associatedFirstFiltrationSequence {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    FilteredComplex.AssociatedSpectralSequence
      (First.Filtration.total (homBicomplex f F)) :=
  Classical.choice (FilteredComplex.AssociatedSpectralSequence.nonempty _)

/-- The first filtration of the Hom bicomplex is associated to the chosen cohomological
spectral sequence. -/
theorem associatedFirstFiltrationSequence_isAssociated {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    FilteredComplex.IsAssociated (First.Filtration.total (homBicomplex f F))
      (associatedFirstFiltrationSequence f F).sequence :=
  sorry

/-- The inclusion of first-quadrant bidegrees `ℕ × ℕ` into `ℤ × ℤ` is injective. -/
theorem spectralSequenceNatEmbedding_injective (r : ℤ) :
    Function.Injective (fun pq : ℕ × ℕ ↦ ((pq.1 : ℤ), (pq.2 : ℤ))) :=
  sorry

/-- First-quadrant page shapes embed into unbounded cohomological page shapes. -/
theorem spectralSequenceNatEmbedding_rel_iff (r : ℤ) (a b : ℕ × ℕ) :
    (spectralSequenceNat ⟨r, 1 - r⟩).Rel a b ↔
      (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (a.1, a.2) (b.1, b.2) :=
  sorry

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
  sorry

/-- Evaluation of the first-quadrant page embedding. -/
theorem spectralSequenceNatEmbedding_f (r : ℤ) (p q : ℕ) :
    (spectralSequenceNatEmbedding r).f (p, q) = ((p : ℤ), (q : ℤ)) :=
  sorry

/-- A page index at least one is at least the initial page zero. -/
theorem zero_le_of_one_le {r : ℤ} (hr : 1 ≤ r) : (0 : ℤ) ≤ r :=
  sorry

/-- The successor page remains at least zero. -/
theorem zero_le_page_succ_of_one_le {r r' : ℤ} (hr : 1 ≤ r) (hrr' : r + 1 = r') :
    (0 : ℤ) ≤ r' :=
  sorry

/-- Objects outside the first quadrant vanish. This concerns objects, not
false equalities between the natural and integer predecessor indices. -/
def PageSupportedInFirstQuadrant (r : ℤ)
    (K : HomologicalComplex AddCommGrpCat.{u + 1} (up' (⟨r, 1 - r⟩ : ℤ × ℤ))) : Prop :=
  ∀ pq : ℤ × ℤ, pq.1 < 0 ∨ pq.2 < 0 → IsZero (K.X pq)

/-- Compare the actual homology short complexes under restriction. The middle
map is identity. A neighbour outside the quadrant receives the zero map; a
neighbour inside the quadrant receives the canonical equality transport. -/
noncomputable def firstQuadrantShortMap (r : ℤ)
    (K : HomologicalComplex AddCommGrpCat.{u + 1} (up' (⟨r, 1 - r⟩ : ℤ × ℤ)))
    (hK : PageSupportedInFirstQuadrant r K) (pq : ℕ × ℕ) :
    (K.restriction (spectralSequenceNatEmbedding r)).sc pq ⟶
      K.sc ((pq.1 : ℤ), (pq.2 : ℤ)) where
  τ₁ := if h : (spectralSequenceNatEmbedding r).f
        ((spectralSequenceNat ⟨r, 1 - r⟩).prev pq) =
        (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (pq.1, pq.2)
      then eqToHom (congrArg K.X h) else 0
  τ₂ := 𝟙 _
  τ₃ := if h : (spectralSequenceNatEmbedding r).f
        ((spectralSequenceNat ⟨r, 1 - r⟩).next pq) =
        (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (pq.1, pq.2)
      then eqToHom (congrArg K.X h) else 0
  comm₁₂ := sorry
  comm₂₃ := sorry

/-- Deleting only zero boundary objects preserves homology via the displayed
short-complex map. -/
instance firstQuadrantShortMap_homology_isIso (r : ℤ)
    (K : HomologicalComplex AddCommGrpCat.{u + 1} (up' (⟨r, 1 - r⟩ : ℤ × ℤ)))
    (hK : PageSupportedInFirstQuadrant r K) (pq : ℕ × ℕ) :
    IsIso (ShortComplex.homologyMap (firstQuadrantShortMap r K hK pq)) :=
  sorry

/-- Homology of a supported restricted page identifies with the next page
through the specified boundary-aware comparison, followed by E.iso. -/
noncomputable def firstQuadrantSequence_pageHomologyIso
    (E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0)
    (r r' : ℤ) (pq : ℕ × ℕ) (hrr' : r + 1 = r') (hr : 1 ≤ r)
    (hK : PageSupportedInFirstQuadrant r (E.page r (zero_le_of_one_le hr))) :
    ((E.page r (zero_le_of_one_le hr)).restriction
        (spectralSequenceNatEmbedding r)).homology pq ≅
      ((E.page r' (zero_le_page_succ_of_one_le hr hrr')).restriction
        (spectralSequenceNatEmbedding r')).X pq :=
  @asIso _ _ _ _ (ShortComplex.homologyMap
    (firstQuadrantShortMap r (E.page r (zero_le_of_one_le hr)) hK pq))
    (firstQuadrantShortMap_homology_isIso r (E.page r (zero_le_of_one_le hr)) hK pq) ≪≫
      E.iso r r' (pq.1, pq.2) hrr' (zero_le_of_one_le hr)

/-- Restrict a sequence whose pages from E1 onward are supported in the first
quadrant. Boundary terms are handled by the specified homology comparison. -/
noncomputable def firstQuadrantSequence
    (E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0)
    (hE : ∀ r (hr : 1 ≤ r),
      PageSupportedInFirstQuadrant r (E.page r (zero_le_of_one_le hr))) :
    CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1 where
  page r hr :=
    (E.page r (zero_le_of_one_le hr)).restriction (spectralSequenceNatEmbedding r)
  iso r r' pq hrr' hr :=
    firstQuadrantSequence_pageHomologyIso E r r' pq hrr' hr (hE r hr)

/-- The restricted pages are exactly the restrictions of the original pages. -/
theorem firstQuadrantSequence_page
    (E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0)
    (hE : ∀ r (hr : 1 ≤ r),
      PageSupportedInFirstQuadrant r (E.page r (zero_le_of_one_le hr)))
    (r : ℤ) (hr : 1 ≤ r) :
    (firstQuadrantSequence E hE).page r hr =
      (E.page r (zero_le_of_one_le hr)).restriction (spectralSequenceNatEmbedding r) :=
  rfl

/-- The first-filtration sequence of the actual first-quadrant Hom bicomplex
vanishes outside that quadrant from E1 onward. -/
theorem associatedFirstFiltrationSequence_supported {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] (r : ℤ) (hr : 1 ≤ r) :
    PageSupportedInFirstQuadrant r
      ((associatedFirstFiltrationSequence f F).sequence.page r (zero_le_of_one_le hr)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
