/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Diagram
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TargetLocus
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant

/-!
# Invariant target loci in groupoid schemes

This module proves that target loci of target-local morphism properties are invariant under a
groupoid scheme when its source and target maps are covers in a standard topology.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- If the source and target maps of a groupoid scheme are covers in a standard topology, the
maximal target-open locus on which the source map has a target-local property is invariant. -/
theorem isOpenInvariant_targetLocus_source {S : Scheme.{u}}
    (G : GroupoidScheme S) (τ : StandardTopology)
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget τ.precoverage]
    (hs : Presieve.singleton G.s.left ∈ τ.precoverage G.U.left)
    (ht : Presieve.singleton G.t.left ∈ τ.precoverage G.U.left) :
    G.toPreRelation.IsOpenInvariant (P.targetLocus G.s.left) := by
  rw [Scheme.PreRelation.isOpenInvariant_iff, Scheme.PreRelation.isSetInvariant_iff]
  have hMain :
      ∀ r : G.R.left,
        G.s.left.base r ∈ P.targetLocus G.s.left →
          G.t.left.base r ∈ P.targetLocus G.s.left := by
    have hnonZariski {τ : StandardTopology} [P.IsLocalAtTarget τ.precoverage]
        (hτ : τ ≠ .zariski)
        (hs_prop : τ.precoverage.morphismProperty G.s.left)
        (ht_prop : τ.precoverage.morphismProperty G.t.left) :
        ∀ r : G.R.left,
          G.s.left.base r ∈ P.targetLocus G.s.left →
            G.t.left.base r ∈ P.targetLocus G.s.left := by
      have hProjection :
          IsPullback (Over.Hom.left (pullback.fst G.s G.t))
            (Over.Hom.left (pullback.snd G.s G.t)) G.s.left G.t.left := by
        simpa using (G.fstSndIsPullback.map (Over.forget S))
      have hComp :
          IsPullback G.c.left (Over.Hom.left (pullback.snd G.s G.t))
            G.s.left G.s.left := by
        simpa using (G.compSndIsPullback.map (Over.forget S))
      have hsEq :
          G.s.left ⁻¹ᵁ P.targetLocus G.s.left =
            P.targetLocus (Over.Hom.left (pullback.snd G.s G.t)) := by
        simpa using P.targetLocus_preimage_of_isPullback_nonZariski
          τ hτ hComp hs_prop
      have htEq :
          G.t.left ⁻¹ᵁ P.targetLocus G.s.left =
            P.targetLocus (Over.Hom.left (pullback.snd G.s G.t)) := by
        simpa using P.targetLocus_preimage_of_isPullback_nonZariski
          τ hτ hProjection ht_prop
      intro r hr
      have hr' : r ∈ P.targetLocus (Over.Hom.left (pullback.snd G.s G.t)) := by
        have hr_source : r ∈ G.s.left ⁻¹ᵁ P.targetLocus G.s.left := hr
        rw [hsEq] at hr_source
        exact hr_source
      have hr_target : r ∈ G.t.left ⁻¹ᵁ P.targetLocus G.s.left := by
        rw [htEq]
        exact hr'
      exact hr_target
    cases τ with
    | zariski =>
      -- Local instance justification (defeq pin): the StandardTopology.zariski precoverage alias is pinned to Scheme.zariskiPrecoverage for the target-locus pullback theorem.
      letI : P.IsLocalAtTarget Scheme.zariskiPrecoverage := by
        simpa [StandardTopology.precoverage] using
          (inferInstance : P.IsLocalAtTarget StandardTopology.zariski.precoverage)
      -- Local instance justification (proof-local temporary data): hs supplies the source open-immersion fact only for this branch.
      letI : IsOpenImmersion G.s.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @IsOpenImmersion) G.s.left).1 hs).2
      -- Local instance justification (proof-local temporary data): ht supplies the target open-immersion fact only for this branch.
      letI : IsOpenImmersion G.t.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @IsOpenImmersion) G.t.left).1 ht).2
      have hProjection :
          IsPullback (Over.Hom.left (pullback.fst G.s G.t))
            (Over.Hom.left (pullback.snd G.s G.t)) G.s.left G.t.left := by
        simpa using (G.fstSndIsPullback.map (Over.forget S))
      have hComp :
          IsPullback G.c.left (Over.Hom.left (pullback.snd G.s G.t))
            G.s.left G.s.left := by
        simpa using (G.compSndIsPullback.map (Over.forget S))
      have hsEq :
          G.s.left ⁻¹ᵁ P.targetLocus G.s.left =
            P.targetLocus (Over.Hom.left (pullback.snd G.s G.t)) := by
        simpa using P.targetLocus_preimage_of_isPullback_zariski hComp
      have htEq :
          G.t.left ⁻¹ᵁ P.targetLocus G.s.left =
            P.targetLocus (Over.Hom.left (pullback.snd G.s G.t)) := by
        simpa using P.targetLocus_preimage_of_isPullback_zariski hProjection
      intro r hr
      have hr' : r ∈ P.targetLocus (Over.Hom.left (pullback.snd G.s G.t)) := by
        have hr_source : r ∈ G.s.left ⁻¹ᵁ P.targetLocus G.s.left := hr
        rw [hsEq] at hr_source
        exact hr_source
      have hr_target : r ∈ G.t.left ⁻¹ᵁ P.targetLocus G.s.left := by
        rw [htEq]
        exact hr'
      exact hr_target
    | etale =>
      have hs_prop : StandardTopology.etale.precoverage.morphismProperty G.s.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @Etale) G.s.left).1 hs).2
      have ht_prop : StandardTopology.etale.precoverage.morphismProperty G.t.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @Etale) G.t.left).1 ht).2
      exact hnonZariski (by simp) hs_prop ht_prop
    | smooth =>
      have hs_prop : StandardTopology.smooth.precoverage.morphismProperty G.s.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @Smooth) G.s.left).1 hs).2
      have ht_prop : StandardTopology.smooth.precoverage.morphismProperty G.t.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @Smooth) G.t.left).1 ht).2
      exact hnonZariski (by simp) hs_prop ht_prop
    | syntomic =>
      have hs_prop : StandardTopology.syntomic.precoverage.morphismProperty G.s.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @Syntomic) G.s.left).1 hs).2
      have ht_prop : StandardTopology.syntomic.precoverage.morphismProperty G.t.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff (P := @Syntomic) G.t.left).1 ht).2
      exact hnonZariski (by simp) hs_prop ht_prop
    | fppf =>
      have hs_prop : StandardTopology.fppf.precoverage.morphismProperty G.s.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff
            (P := fun {X Y} (f : X ⟶ Y) ↦ Flat f ∧ LocallyOfFinitePresentation f)
            G.s.left).1 hs).2
      have ht_prop : StandardTopology.fppf.precoverage.morphismProperty G.t.left := by
        simpa [StandardTopology.morphismProperty_iff] using
          ((Scheme.singleton_mem_precoverage_iff
            (P := fun {X Y} (f : X ⟶ Y) ↦ Flat f ∧ LocallyOfFinitePresentation f)
            G.t.left).1 ht).2
      exact hnonZariski (by simp) hs_prop ht_prop
  intro r hr
  rw [G.toPreRelation_s] at hr
  rw [G.toPreRelation_t]
  exact hMain r hr

/-- If the source and target maps of a groupoid scheme are covers in a non-Zariski standard
topology, the maximal target-open locus on which its stabilizer map has a target-local property
is invariant. -/
theorem isOpenInvariant_targetLocus_stabilizerMap {S : Scheme.{u}}
    (G : GroupoidScheme S) (τ : StandardTopology) (hτ : τ ≠ .zariski)
    (P : MorphismProperty Scheme.{u}) [P.IsLocalAtTarget τ.precoverage]
    (hs : Presieve.singleton G.s.left ∈ τ.precoverage G.U.left)
    (ht : Presieve.singleton G.t.left ∈ τ.precoverage G.U.left) :
    G.toPreRelation.IsOpenInvariant (P.targetLocus G.stabilizerMap.left) := sorry

end AlgebraicGeometry.GroupoidScheme
