/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complete intersections over a field

This module owns the global and local complete-intersection conditions for
algebras over a field.
-/

universe u v

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- A `k`-algebra is a global complete intersection when it is subsingleton or
admits a presentation with `c ≤ n` relations and variables and with presentation
dimension equal to its Krull dimension. -/
@[stacks 00S9]
class IsGlobalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  /-- A presentation with `c ≤ n` and the expected dimension, unless the algebra is subsingleton. -/
  presentation_or_subsingleton :
    Subsingleton S ∨
      ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
        c ≤ n ∧ ringKrullDim S = P.dimension

/-- The global complete-intersection condition is exactly the existence of a presentation with
`c ≤ n` and the expected dimension, together with the subsingleton convention. -/
@[stacks 00S9 "global complete-intersection specification"]
theorem isGlobalCompleteIntersection_iff :
    IsGlobalCompleteIntersection k S ↔
      Subsingleton S ∨
        ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
          c ≤ n ∧ ringKrullDim S = P.dimension := by
  exact ⟨fun h ↦ h.presentation_or_subsingleton, fun h ↦ ⟨h⟩⟩

namespace IsGlobalCompleteIntersection

/-- Build a global complete intersection from a presentation with `c ≤ n` and the
dimension criterion, or from the subsingleton convention. -/
theorem of_presentation_or_subsingleton
    (h : Subsingleton S ∨
      ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
        c ≤ n ∧ ringKrullDim S = P.dimension) :
    IsGlobalCompleteIntersection k S := by
  exact ⟨h⟩

/-- Global complete intersections are invariant under equivalences of `k`-algebras. -/
theorem of_algEquiv {T : Type*} [CommRing T] [Algebra k T]
    (hS : IsGlobalCompleteIntersection k S) (e : S ≃ₐ[k] T) :
    IsGlobalCompleteIntersection k T := by
  refine ⟨?_⟩
  rcases hS.presentation_or_subsingleton with h | ⟨n, c, P, hcn, hdim⟩
  · show Subsingleton T ∨ _
    exact Or.inl ⟨fun x y ↦ e.symm.injective (h.elim _ _)⟩
  · show Subsingleton T ∨ _
    refine Or.inr ⟨n, c, P.ofAlgEquiv e, hcn, ?_⟩
    rw [← e.toRingEquiv.ringKrullDim]
    exact hdim

/-- A global complete-intersection algebra is finitely presented over its base field. -/
instance instFinitePresentation [h : IsGlobalCompleteIntersection k S] :
    Algebra.FinitePresentation k S := by
  rcases h.presentation_or_subsingleton with hS | ⟨n, c, P, _, _⟩
  · show Algebra.FinitePresentation k S
    letI := hS
    exact Algebra.FinitePresentation.of_finiteType.mp
      (Algebra.FiniteType.of_surjective (Algebra.ofId k S)
        (Function.surjective_to_subsingleton _))
  · show Algebra.FinitePresentation k S
    exact P.finitePresentation_of_isFinite

/-- A global complete intersection is subsingleton or has a quotient presentation with `c ≤ n`
relations and Krull dimension `n - c`. -/
theorem quotientPresentation_or_subsingleton [IsGlobalCompleteIntersection k S] :
    Subsingleton S ∨
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k),
        Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] S) ∧
          c ≤ n ∧ ringKrullDim S = n - c := by
  rcases presentation_or_subsingleton (k := k) (S := S) with hS | ⟨n, c, P, hcn, hdim⟩
  · show Subsingleton S ∨ _
    exact Or.inl hS
  · show Subsingleton S ∨ _
    refine Or.inr ⟨n, c, P.relation, ?_, hcn, ?_⟩
    · change Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[k] S)
      exact ⟨(Ideal.quotientEquivAlgOfEq k P.span_range_relation_eq_ker).trans
        (P.quotientEquiv.restrictScalars k)⟩
    · show ringKrullDim S = n - c
      simpa [Algebra.Presentation.dimension] using hdim

/-- Subsingleton algebras are global complete intersections by convention. -/
instance instOfSubsingleton [Subsingleton S] : IsGlobalCompleteIntersection k S := by
  exact ⟨Or.inl inferInstance⟩

end IsGlobalCompleteIntersection

/-- A `k`-algebra is a local complete intersection when finitely many basic
opens cover its spectrum and each corresponding localization is a global
complete intersection. -/
@[stacks 00S9]
class IsLocalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  /-- A finite basic-open cover by global complete intersections. -/
  exists_basicOpen_cover :
    ∃ s : Finset S,
      Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)

/-- The local complete-intersection condition is exactly the existence of a finite basic-open
cover by global complete intersections. -/
@[stacks 00S9 "local complete-intersection specification over a field"]
theorem isLocalCompleteIntersection_iff :
    IsLocalCompleteIntersection k S ↔
      ∃ s : Finset S, Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g) := by
  exact ⟨fun h ↦ h.exists_basicOpen_cover, fun h ↦ ⟨h⟩⟩

namespace IsLocalCompleteIntersection

/-- Build a local complete intersection from a finite basic-open cover by global complete
intersections. -/
theorem of_basicOpen_cover
    (h : ∃ s : Finset S, Ideal.span (s : Set S) = ⊤ ∧
      ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)) :
    IsLocalCompleteIntersection k S := by
  exact ⟨h⟩

/-- A local complete-intersection algebra is finitely presented over its base field. -/
instance instFinitePresentation [h : IsLocalCompleteIntersection k S] :
    Algebra.FinitePresentation k S := by
  obtain ⟨s, hs, hloc⟩ := h.exists_basicOpen_cover
  apply Algebra.FinitePresentation.of_span_eq_top_target (s : Set S) hs
  intro g hg
  letI := hloc g hg
  infer_instance

/-- Every global complete intersection is a local complete intersection. -/
instance instOfGlobal [IsGlobalCompleteIntersection k S] :
    IsLocalCompleteIntersection k S := by
  classical
  refine ⟨⟨{1}, ?_, ?_⟩⟩
  · show Ideal.span (({1} : Finset S) : Set S) = ⊤
    simpa using (Ideal.span_singleton_one : Ideal.span ({1} : Set S) = ⊤)
  · show ∀ g ∈ ({1} : Finset S), IsGlobalCompleteIntersection k (Localization.Away g)
    intro g hg
    have hg1 : g = 1 := Finset.mem_singleton.mp hg
    subst g
    exact IsGlobalCompleteIntersection.of_algEquiv inferInstance
      ((IsLocalization.atOne S (Localization.Away (1 : S))).restrictScalars k)

end IsLocalCompleteIntersection
