/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Colimit.Ring
public import ReasLib.Algebra.WLocalHull.Stage

/-!
# W-localization of a commutative ring

The w-localization of a commutative ring is the filtered colimit of its
finite-stage algebras over finite subsets ordered by inclusion.
-/

@[expose] public section

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A]

/-- Restriction of a vanishing pattern to a finite subset by intersection. -/
noncomputable def Pattern.restrict (E₁ : Finset A) {E₂ : Finset A} (p : Pattern A E₂) :
    Pattern A E₁ :=
  open Classical in ⟨E₁ ∩ p.1, Finset.inter_subset_left⟩

/-- The specializing submonoid of a restricted pattern is contained in the
specializing submonoid of the finer pattern. -/
theorem specializingSubmonoid_mono {E₁ E₂ : Finset A} (hE : E₁ ⊆ E₂) (p : Pattern A E₂) :
    specializingSubmonoid A (Pattern.restrict A E₁ p).elem (Pattern.restrict A E₁ p).span ≤
      (specializingSubmonoid A p.elem p.span).comap (RingHom.id A) := by
  classical
  have span_le : (Pattern.restrict A E₁ p).span ≤ p.span := by
    apply Ideal.span_mono
    intro element element_mem
    simp only [Pattern.restrict, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_inter] at element_mem ⊢
    exact ⟨hE element_mem.1, fun pattern_mem ↦ element_mem.2 ⟨element_mem.1, pattern_mem⟩⟩
  have elem_dvd : (Pattern.restrict A E₁ p).elem ∣ p.elem :=
    Finset.prod_dvd_prod_of_subset (E₁ ∩ p.1) p.1 (fun element ↦ element)
      Finset.inter_subset_right
  let quotientMap := Ideal.Quotient.factor span_le
  let stratumMap :=
    (algebraMap (A ⧸ p.span) (stratumSections A p.elem p.span)).comp quotientMap
  have generator_isUnit :
      IsUnit (stratumMap (Ideal.Quotient.mk (Pattern.restrict A E₁ p).span
        (Pattern.restrict A E₁ p).elem)) := by
    change IsUnit (algebraMap (A ⧸ p.span) (stratumSections A p.elem p.span)
      (Ideal.Quotient.mk p.span (Pattern.restrict A E₁ p).elem))
    exact IsLocalization.Away.isUnit_of_dvd (Ideal.Quotient.mk p.span p.elem)
      (map_dvd (Ideal.Quotient.mk p.span) elem_dvd)
  let localizationMap :
      stratumSections A (Pattern.restrict A E₁ p).elem (Pattern.restrict A E₁ p).span →+*
        stratumSections A p.elem p.span :=
    IsLocalization.Away.lift
      (Ideal.Quotient.mk (Pattern.restrict A E₁ p).span (Pattern.restrict A E₁ p).elem)
      generator_isUnit
  intro element element_mem
  change IsUnit (toStratumSections A p.elem p.span element)
  change IsUnit (toStratumSections A (Pattern.restrict A E₁ p).elem
    (Pattern.restrict A E₁ p).span element) at element_mem
  simpa only [toStratumSections, RingHom.comp_apply, localizationMap,
    IsLocalization.Away.lift_eq, stratumMap, quotientMap, Ideal.Quotient.factor_mk] using
    element_mem.map localizationMap

/-- The localization map induced by refinement of finite subsets and the
identity ring homomorphism. -/
noncomputable def specializingMap {E₁ E₂ : Finset A} (hE : E₁ ⊆ E₂) (p : Pattern A E₂) :
    specializingLocalization A (Pattern.restrict A E₁ p).elem (Pattern.restrict A E₁ p).span →+*
      specializingLocalization A p.elem p.span :=
  IsLocalization.map (specializingLocalization A p.elem p.span) (RingHom.id A)
    (specializingSubmonoid_mono A hE p)

/-- The transition ring homomorphism between finite-stage algebras for
`E₁ ⊆ E₂`, obtained by restricting patterns and mapping their localizations. -/
noncomputable def stageMap {E₁ E₂ : Finset A} (hE : E₁ ⊆ E₂) : stage A E₁ →+* stage A E₂ :=
  RingHom.pi fun p ↦ (specializingMap A hE p).comp (stage.eval A (Pattern.restrict A E₁ p))

/-- Stage maps form a directed system over finite subsets ordered by inclusion. -/
instance instDirectedSystem :
    DirectedSystem (stage A) (fun _ _ h ↦ stageMap A h) := sorry

/-- The w-localization of a commutative ring is the filtered colimit of
`stage A E` over `E : Finset A`. -/
abbrev wLocalization : Type u :=
  Ring.DirectLimit (stage A) fun _ _ h ↦ stageMap A h

/-- The cocone ring homomorphism from a finite-stage algebra to the w-localization. -/
noncomputable abbrev of (E : Finset A) : stage A E →+* wLocalization A :=
  Ring.DirectLimit.of (stage A) (fun _ _ h ↦ stageMap A h) E

/-- The algebra structure on the w-localization induced through the empty stage. -/
noncomputable instance instAlgebra : Algebra A (wLocalization A) :=
  RingHom.toAlgebra ((of A ∅).comp (algebraMap A (stage A ∅)))

/-- A compatible family of ring homomorphisms from the finite-stage algebras
induces a ring homomorphism from the w-localization. -/
noncomputable abbrev lift {P : Type u} [CommRing P] (g : ∀ E, stage A E →+* P)
    (Hg : ∀ E₁ E₂ h x, g E₂ (stageMap A h x) = g E₁ x) : wLocalization A →+* P :=
  Ring.DirectLimit.lift (stage A) (fun _ _ h ↦ stageMap A h) P g Hg

/-- Cocone maps are compatible with stage transitions. -/
theorem of_stageMap {E₁ E₂ : Finset A} (hE : E₁ ⊆ E₂) (x : stage A E₁) :
    of A E₂ (stageMap A hE x) = of A E₁ x := sorry

/-- Ring homomorphisms from the w-localization are determined by their
composites with all finite-stage cocone maps. -/
theorem hom_ext {P : Type u} [CommRing P] {g₁ g₂ : wLocalization A →+* P}
    (h : ∀ E, g₁.comp (of A E) = g₂.comp (of A E)) : g₁ = g₂ := sorry

/-- The colimit lift recovers the given ring homomorphism on each finite stage. -/
theorem lift_of {P : Type u} [CommRing P] (g : ∀ E, stage A E →+* P)
    (Hg : ∀ E₁ E₂ h x, g E₂ (stageMap A h x) = g E₁ x) (E : Finset A) (x : stage A E) :
    lift A g Hg (of A E x) = g E x := sorry

end Algebra.WLocalHull
