module

public import Mathlib.Topology.Algebra.Group.Extension
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Galois.KrullTopology

@[expose] public section

universe u v

namespace FieldExtension

open AlgEquiv InfiniteGalois

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]
variable (M : IntermediateField K L)
variable [IsGalois K L] [Normal K M]

/-- Lemma 9.22.5 (Tag 0BMM): in a Galois extension `L/K`, the inclusion
`Gal(L / M) → Gal(L / K)` and restriction `Gal(L / K) → Gal(M / K)` form a short exact sequence
of profinite topological groups. -/
theorem galoisTowerIsShortExact :
    TopologicalGroup.IsSES
      (MulSemiringAction.toAlgAut Gal(L / M) K L)
      (restrictNormalHom M) := by
  have hInclusionContinuous :
      Continuous (MulSemiringAction.toAlgAut Gal(L / M) K L) := by
    -- Local instance justification (proof-local temporary data): view the ambient field discretely to apply the action-continuity bridge.
    letI : TopologicalSpace L := ⊥
    -- Local instance justification (proof-local temporary data): equip the temporary discrete topology with its canonical instance.
    letI : DiscreteTopology L := ⟨rfl⟩
    refine continuousOfContinuousGaloisAction
      (g := MulSemiringAction.toAlgAut Gal(L / M) K L) ?_
    simpa using (continuous_smul : Continuous fun p : Gal(L / M) × L ↦ p.1 • p.2)
  have hInclusionRange :
      (MulSemiringAction.toAlgAut Gal(L / M) K L).range = M.fixingSubgroup := by
    ext σ
    constructor
    · rintro ⟨τ, rfl⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      simpa using τ.commutes ⟨x, hx⟩
    · intro hσ
      refine ⟨IntermediateField.fixingSubgroupEquiv M ⟨σ, hσ⟩, ?_⟩
      ext x
      rfl
  have hInclusionInjective :
      Function.Injective (MulSemiringAction.toAlgAut Gal(L / M) K L) := by
    intro σ τ hστ
    ext x
    exact congrArg (fun f : Gal(L / K) => f x) hστ
  have hInclusionClosedEmbedding :
      Topology.IsClosedEmbedding (MulSemiringAction.toAlgAut Gal(L / M) K L) := by
    exact Continuous.isClosedEmbedding hInclusionContinuous hInclusionInjective
  have hRestrictOpenQuotient :
      IsOpenQuotientMap (restrictNormalHom M : Gal(L / K) →* Gal(M / K)) := by
    apply MonoidHom.isOpenQuotientMap_of_isQuotientMap
    exact Topology.IsQuotientMap.of_surjective_continuous
      (by
        simpa using (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L)))
      (by
        simpa using (InfiniteGalois.restrictNormalHom_continuous (k := K) (K := L) M))
  refine TopologicalGroup.IsSES.mk hInclusionClosedEmbedding hRestrictOpenQuotient ?_
  rw [MonoidHom.mulExact_iff, IntermediateField.restrictNormalHom_ker, hInclusionRange]

end

end FieldExtension
