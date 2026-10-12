/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpace.AdicDiagram
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Recover a ring map from the actual adic presentation

The input is a morphism from a presentation cocone point to the representable
functor of `Spec(A)` over `S`. Yoneda and the proved Γ/Spec adjunction recover
each quotient-ring map. Naturality gives compatibility; completeness recovers
the ring map into `B`. There is no stagewise choice of scheme isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AdicPresentation

variable {A B : Type u} [CommRing A] [CommRing B] {S : Scheme.{u}}
variable (hB : Spec (.of B) ⟶ S) (I : Ideal B)
variable (c : Cocone (diagram hB I ⋙ yoneda))
variable {hA : Spec (.of A) ⟶ S} (q : c.pt ⟶ yoneda.obj (Over.mk hA))

/-- The actual morphism of the `n`th quotient stage into `Spec(A)`, over `S`. -/
def stageToBase (n : ℕ) : (diagram hB I).obj n ⟶ Over.mk hA :=
  yoneda.preimage (c.ι.app n ≫ q)

/-- Applying Yoneda returns the original presentation leg followed by `q`. -/
theorem stageToBase_yoneda (n : ℕ) :
    yoneda.map (stageToBase hB I c q n) = c.ι.app n ≫ q :=
  yoneda.map_preimage _

/-- The actual stage-to-base maps commute with quotient transitions. -/
theorem stageToBase_natural {i j : ℕ} (f : i ⟶ j) :
    (diagram hB I).map f ≫ stageToBase hB I c q j = stageToBase hB I c q i := by
  apply yoneda.map_injective
  rw [Functor.map_comp, stageToBase_yoneda, stageToBase_yoneda]
  exact c.w_assoc f q

/-- The quotient-ring structure map recovered by the actual Spec equivalence. -/
def stageRingHom (n : ℕ) : A →+* B ⧸ I ^ (n + 1) :=
  (Spec.preimage (stageToBase hB I c q n).left).hom

/-- The spectrum of the recovered homomorphism is exactly the original stage map. -/
theorem stageRingHom_spec (n : ℕ) :
    Spec.map (CommRingCat.ofHom (stageRingHom hB I c q n)) =
      (stageToBase hB I c q n).left :=
  Spec.map_preimage _

/-- Compatibility of the recovered ring maps is proved from the cocone law. -/
theorem stageRingHom_compatible {i j : ℕ} (h : i ≤ j) :
    (Ideal.Quotient.factorPow I (Nat.succ_le_succ h)).comp
        (stageRingHom hB I c q j) = stageRingHom hB I c q i := by
  suffices he : CommRingCat.ofHom ((Ideal.Quotient.factorPow I (Nat.succ_le_succ h)).comp
      (stageRingHom hB I c q j)) = CommRingCat.ofHom (stageRingHom hB I c q i) by
    exact congrArg CommRingCat.Hom.hom he
  apply Spec.map_injective
  rw [CommRingCat.ofHom_comp, Spec.map_comp, stageRingHom_spec, stageRingHom_spec]
  exact congrArg Over.Hom.left (stageToBase_natural hB I c q (homOfLE h))

/-- The compatible family extended to include the zero-th quotient. -/
def stageFamily (n : ℕ) : A →+* B ⧸ I ^ n :=
  (Ideal.Quotient.factorPow I n.le_succ).comp (stageRingHom hB I c q n)

/-- Extending the indexing does not change any positive quotient map. -/
theorem stageFamily_succ (n : ℕ) :
    stageFamily hB I c q (n + 1) = stageRingHom hB I c q n :=
  stageRingHom_compatible hB I c q n.le_succ

/-- The extended family satisfies the full inverse-system compatibility law. -/
theorem stageFamily_compatible {i j : ℕ} (h : i ≤ j) :
    (Ideal.Quotient.factorPow I h).comp (stageFamily hB I c q j) =
      stageFamily hB I c q i := by
  apply RingHom.ext
  intro a
  have hc := RingHom.congr_fun (stageRingHom_compatible hB I c q h) a
  simp only [RingHom.comp_apply] at hc
  change Ideal.Quotient.factorPow I h
      (Ideal.Quotient.factorPow I j.le_succ (stageRingHom hB I c q j a)) =
    Ideal.Quotient.factorPow I i.le_succ (stageRingHom hB I c q i a)
  rw [← hc]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_apply]

/-- The ring map into the actual adic completion, obtained from compatible sections. -/
def completedStructureMap : A →+* AdicCompletion I B :=
  AdicCompletion.liftRingHom I (stageFamily hB I c q)
    (stageFamily_compatible hB I c q)

/-- Evaluation of the completion map recovers each original positive stage. -/
theorem completedStructureMap_eval (n : ℕ) :
    (AdicCompletion.evalₐ I (n + 1)).toRingHom.comp
        (completedStructureMap hB I c q) = stageRingHom hB I c q n := by
  apply RingHom.ext
  intro a
  change AdicCompletion.evalₐ I (n + 1) (completedStructureMap hB I c q a) = _
  simpa only [completedStructureMap, AdicCompletion.evalₐ_liftRingHom] using
    RingHom.congr_fun (stageFamily_succ hB I c q n) a

/-- The structure map into the complete presenting ring itself. -/
def structureMap [IsAdicComplete I B] : A →+* B :=
  (AdicCompletion.ofAlgEquiv I).symm.toRingEquiv.toRingHom.comp
    (completedStructureMap hB I c q)

/-- Reduction of the recovered structure map gives exactly the original stage map. -/
theorem structureMap_mod [IsAdicComplete I B] (n : ℕ) :
    (Ideal.Quotient.mk (I ^ (n + 1))).comp (structureMap hB I c q) =
      stageRingHom hB I c q n := by
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (I ^ (n + 1))
      ((AdicCompletion.ofAlgEquiv I).symm (completedStructureMap hB I c q a)) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  exact RingHom.congr_fun (completedStructureMap_eval hB I c q n) a

/-- The recovered ring map reproduces the original geometric map on every stage. -/
theorem structureMap_stage [IsAdicComplete I B] (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫
        Spec.map (CommRingCat.ofHom (structureMap hB I c q)) =
      (stageToBase hB I c q n).left := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, structureMap_mod, stageRingHom_spec]

/-- The complete-ring map is uniquely determined by its actual positive stages. -/
theorem structureMap_unique [IsAdicComplete I B] (φ : A →+* B)
    (hφ : ∀ n, (Ideal.Quotient.mk (I ^ (n + 1))).comp φ = stageRingHom hB I c q n) :
    φ = structureMap hB I c q := by
  apply RingHom.ext
  intro a
  apply (AdicCompletion.ofAlgEquiv I).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [AdicCompletion.ofAlgEquiv_apply, AdicCompletion.evalₐ_of]
  have hn := RingHom.congr_fun ((hφ n).trans (structureMap_mod hB I c q n).symm) a
  exact congrArg (Ideal.Quotient.factorPow I n.le_succ) hn

/-- Stagewise nilpotence of the base ideal implies continuity in the adic topologies.
The geometric application must obtain this condition from the map to `Spf(A)`. -/
theorem structureMap_continuous [IsAdicComplete I B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (m : Ideal A) (hm : IsAdic m) (hI : IsAdic I)
    (hstage : ∀ n, ∃ k, m ^ k ≤ RingHom.ker (stageRingHom hB I c q n)) :
    Continuous (structureMap hB I c q) := by
  apply continuous_of_continuousAt_zero (structureMap hB I c q).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  apply (hm.hasBasis_nhds_zero.tendsto_iff hI.hasBasis_nhds_zero).mpr
  intro n hn
  obtain ⟨k, hk⟩ := hstage n
  refine ⟨k, trivial, ?_⟩
  intro a ha
  have haz : stageRingHom hB I c q n a = 0 := hk ha
  have hmod := RingHom.congr_fun (structureMap_mod hB I c q n) a
  have hin : structureMap hB I c q a ∈ I ^ (n + 1) :=
    Ideal.Quotient.eq_zero_iff_mem.mp (hmod.trans haz)
  exact Ideal.pow_le_pow_right n.le_succ hin

end AlgebraicGeometry.AdicPresentation
