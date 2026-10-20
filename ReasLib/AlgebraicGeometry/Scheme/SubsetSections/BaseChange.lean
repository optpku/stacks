module

public import ReasLib.Algebra.Category.CommAlgCat.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.SubsetSections
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Flat base change for sections on subsets

This module compares structure-sheaf sections on compact-open directed intersections under flat
affine base change and derives the corresponding tensor-product description.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {X Y : Scheme.{u}}

/-- A nonempty intersection of compact opens on a quasi-separated scheme admits a directed
compact-open presentation. -/
private theorem existsCompactOpenDirectedIntersectionOfExistsIInter
    [QuasiSeparatedSpace Y] (E : Set Y)
    (hE : ∃ S : Set (CompactOpens Y), S.Nonempty ∧ E = ⋂ U ∈ S, (U : Set Y)) :
    ∃ S : Set (CompactOpens Y), IsCompactOpenDirectedIntersection E S := by
  classical
  rcases hE with ⟨S, hS_nonempty, hS_eq⟩
  have hfiniteInter
      (t : { t : Finset (CompactOpens Y) // t.Nonempty ∧ ∀ U ∈ t, U ∈ S }) :
      (((t.1.inf' t.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) =
        ⋂ U ∈ (t : Finset (CompactOpens Y)), (U : Set Y) := by
    ext x
    rw [Finset.apply_inf'_eq_inf'_comp t.2.1 (fun U : CompactOpens Y ↦ (U : Set Y))
      (fun _ _ ↦ rfl)]
    rw [Finset.inf'_eq_inf]
    simp [Set.mem_iInter]
  let T : Set (CompactOpens Y) :=
    Set.range fun t : { t : Finset (CompactOpens Y) // t.Nonempty ∧ ∀ U ∈ t, U ∈ S } ↦
      t.1.inf' t.2.1 (fun W : CompactOpens Y ↦ W)
  refine ⟨T, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hS_nonempty with ⟨U, hU⟩
    refine ⟨(({U} : Finset (CompactOpens Y)).inf' (by simp) (fun W : CompactOpens Y ↦ W)), ?_⟩
    refine ⟨⟨({U} : Finset (CompactOpens Y)), by simp, ?_⟩, rfl⟩
    intro V hV
    simp only [Finset.mem_singleton] at hV
    simpa [hV] using hU
  · ext x
    constructor
    · intro hx
      rw [hS_eq] at hx
      simp only [Set.mem_iInter] at hx ⊢
      intro U hU
      rcases hU with ⟨t, rfl⟩
      rw [show
          (((t.1.inf' t.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) =
            ⋂ V ∈ (t : Finset (CompactOpens Y)), (V : Set Y) from hfiniteInter t]
      simp only [Set.mem_iInter]
      intro V hV
      exact hx V (t.2.2 V hV)
    · intro hx
      rw [hS_eq]
      simp only [Set.mem_iInter] at hx ⊢
      intro U hU
      have h_singleton :
          ((({U} : Finset (CompactOpens Y)).inf' (by simp) (fun W : CompactOpens Y ↦ W) :
            CompactOpens Y)) ∈ T := by
        refine ⟨⟨({U} : Finset (CompactOpens Y)), by simp, ?_⟩, rfl⟩
        intro V hV
        simp only [Finset.mem_singleton] at hV
        simpa [hV] using hU
      have hxU :
          x ∈
            ((({U} : Finset (CompactOpens Y)).inf' (by simp) (fun W : CompactOpens Y ↦ W) :
              CompactOpens Y) : Set Y) :=
        hx ((({U} : Finset (CompactOpens Y)).inf' (by simp) (fun W : CompactOpens Y ↦ W)))
          h_singleton
      simpa using hxU
  · intro U hU V hV
    rcases hU with ⟨s, rfl⟩
    rcases hV with ⟨t, rfl⟩
    let st : { u : Finset (CompactOpens Y) // u.Nonempty ∧ ∀ W ∈ u, W ∈ S } :=
      ⟨s.1 ∪ t.1, s.2.1.mono (by intro W hW; exact Finset.mem_union.mpr (Or.inl hW)), by
        intro W hW
        rcases Finset.mem_union.mp hW with hW | hW
        · exact s.2.2 W hW
        · exact t.2.2 W hW⟩
    refine ⟨st.1.inf' st.2.1 (fun W : CompactOpens Y ↦ W), ?_, ?_, ?_⟩
    · exact ⟨st, rfl⟩
    · intro x hx
      change x ∈
        (((s.1.inf' s.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y))
      rw [show
          (((s.1.inf' s.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) =
            ⋂ W ∈ (s : Finset (CompactOpens Y)), (W : Set Y) from hfiniteInter s]
      change x ∈
        (((st.1.inf' st.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) at hx
      rw [show
          (((st.1.inf' st.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) =
            ⋂ W ∈ (st : Finset (CompactOpens Y)), (W : Set Y) from hfiniteInter st] at hx
      simp only [Set.mem_iInter] at hx ⊢
      intro W hW
      exact hx W (Finset.mem_union.mpr (Or.inl hW))
    · intro x hx
      change x ∈
        (((t.1.inf' t.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y))
      rw [show
          (((t.1.inf' t.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) =
            ⋂ W ∈ (t : Finset (CompactOpens Y)), (W : Set Y) from hfiniteInter t]
      change x ∈
        (((st.1.inf' st.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) at hx
      rw [show
          (((st.1.inf' st.2.1 (fun W : CompactOpens Y ↦ W) : CompactOpens Y) : Set Y)) =
            ⋂ W ∈ (st : Finset (CompactOpens Y)), (W : Set Y) from hfiniteInter st] at hx
      simp only [Set.mem_iInter] at hx ⊢
      intro W hW
      exact hx W (Finset.mem_union.mpr (Or.inr hW))

/-- The inverse image of a compact open under a quasi-compact scheme morphism is compact open. -/
private noncomputable def compactOpenPreimage
    (f : X ⟶ Y) (hf : QuasiCompact f) (U : CompactOpens Y) : CompactOpens X where
  carrier := (f ⁻¹ᵁ U.toOpens : Set X)
  isCompact' := by
    simpa using
      (show IsCompact (f ⁻¹' (U : Set Y)) from
        hf.isCompact_preimage (U : Set Y) U.isOpen U.isCompact)
  isOpen' := (f ⁻¹ᵁ U.toOpens).isOpen

/-- Pulling back a compact-open directed-intersection presentation along a quasi-compact morphism
gives a directed presentation of the inverse image. -/
private theorem preimage_isCompactOpenDirectedIntersection
    (f : X ⟶ Y) (hf : QuasiCompact f) (E : Set Y) (S : Set (CompactOpens Y))
    (hE : IsCompactOpenDirectedIntersection E S) :
    IsCompactOpenDirectedIntersection (f ⁻¹' E) ((compactOpenPreimage (f := f) hf) '' S) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hE.nonempty with ⟨U, hU⟩
    exact ⟨compactOpenPreimage (f := f) hf U, ⟨U, hU, rfl⟩⟩
  · ext x
    constructor
    · intro hx
      rw [Set.mem_preimage] at hx
      simp only [Set.mem_iInter]
      rintro _ ⟨U, hU, rfl⟩
      simpa [compactOpenPreimage] using hE.mem hx hU
    · intro hx
      simp only [Set.mem_iInter] at hx
      rw [Set.mem_preimage, hE.eq_iInter]
      simp only [Set.mem_iInter]
      intro U hU
      simpa [compactOpenPreimage] using hx (compactOpenPreimage (f := f) hf U) ⟨U, hU, rfl⟩
  · intro U hU V hV
    rcases hU with ⟨U₀, hU₀, rfl⟩
    rcases hV with ⟨V₀, hV₀, rfl⟩
    rcases hE.directed U₀ hU₀ V₀ hV₀ with ⟨W, hW, hWU, hWV⟩
    refine
      ⟨compactOpenPreimage (f := f) hf W, ⟨W, hW, rfl⟩,
        show compactOpenPreimage (f := f) hf U₀ ≥ compactOpenPreimage (f := f) hf W from
          show (compactOpenPreimage (f := f) hf W : Set X) ⊆ compactOpenPreimage (f := f) hf U₀
          from by
            intro x hx
            exact hWU hx,
        show compactOpenPreimage (f := f) hf V₀ ≥ compactOpenPreimage (f := f) hf W from
          show (compactOpenPreimage (f := f) hf W : Set X) ⊆ compactOpenPreimage (f := f) hf V₀
          from by
            intro x hx
            exact hWV hx⟩

/-- Flat affine base change carries the algebra of structure-sheaf sections on a compact-open
directed intersection to the corresponding algebra on its inverse image. -/
theorem subsetSectionsAlg_baseChange_of_flat_of_directedIntersection
    (f : X ⟶ Y) (p : X ⟶ Spec (CommRingCat.of B))
    (q : Y ⟶ Spec (CommRingCat.of A))
    (sq : IsPullback p f (Spec.map (CommRingCat.ofHom (algebraMap A B))) q)
    [Module.Flat A B] [QuasiSeparatedSpace Y]
    (E : Set Y) (S : Set (CompactOpens Y))
    (hE : IsCompactOpenDirectedIntersection E S) :
    IsIsomorphic
      ((CommAlgCat.BaseChange.functor (CommRingCat.ofHom (algebraMap A B))).obj
        (subsetSectionsAlg q E))
      (subsetSectionsAlg p (f ⁻¹' E)) := sorry

/-- In a cartesian square over a flat map `A ⟶ B`, sections on the inverse image of a nonempty
intersection of compact opens are the scalar extension of the original subset sections. -/
theorem subsetSections_tensorProduct_of_flat
    (f : X ⟶ Y) (p : X ⟶ Spec (CommRingCat.of B))
    (q : Y ⟶ Spec (CommRingCat.of A))
    (sq : IsPullback p f (Spec.map (CommRingCat.ofHom (algebraMap A B))) q)
    [Module.Flat A B] [QuasiSeparatedSpace Y]
    (E : Set Y)
    (hE : ∃ S : Set (CompactOpens Y), S.Nonempty ∧ E = ⋂ U ∈ S, (U : Set Y)) :
    IsIsomorphic
      (Scheme.subsetSectionsRing X (f ⁻¹' E))
      (CommRingCat.of (TensorProduct A (subsetSectionsAlg q E) B)) := by
  rcases existsCompactOpenDirectedIntersectionOfExistsIInter (Y := Y) E hE with ⟨S, hS⟩
  rcases subsetSectionsAlg_baseChange_of_flat_of_directedIntersection
    f p q sq E S hS with ⟨e⟩
  refine ⟨?_⟩
  exact
    (eqToIso (subsetSectionsAlg_carrier p (f ⁻¹' E)).symm) ≪≫
      (forget₂ (CommAlgCat B) CommRingCat).mapIso e.symm ≪≫
      CommAlgCat.BaseChange.forgetObjIsoTensorProduct
        (A := A) (B := B) (subsetSectionsAlg q E)

end AlgebraicGeometry.Scheme.Hom
