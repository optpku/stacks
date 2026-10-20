module

public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

@[expose] public section

universe u

namespace FieldExtension

/-- A finite family of elements of a characteristic-`p` field acquires `p`th roots after a finite
purely inseparable field extension. -/
theorem existsFinitePurelyInseparableExtensionWithPthRoots
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] (C : Finset k) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
      FiniteDimensional k k' ∧
        IsPurelyInseparable k k' ∧
          ∀ a ∈ C, ∃ b : k', b ^ p = algebraMap k k' a := by
  classical
  -- Local instance justification (proof-local temporary data): use the canonical algebra map from the base field into its characteristic-`p` perfect closure.
  letI : Algebra k (PerfectClosure k p) := (PerfectClosure.of k p).toAlgebra
  -- Local instance justification (proof-local temporary data): expose the perfect-closure Frobenius radical property needed to obtain pure inseparability.
  letI : IsPRadical (algebraMap k (PerfectClosure k p)) p := by
    change IsPRadical (PerfectClosure.of k p) p
    exact PerfectClosure.isPRadical (K := k) (p := p)
  -- Local instance justification (proof-local temporary data): view the perfect closure as a purely inseparable extension while constructing a finite intermediate subfield.
  letI : IsPurelyInseparable k (PerfectClosure k p) :=
    IsPRadical.isPurelyInseparable (K := k) (L := PerfectClosure k p) p
  -- Local instance justification (proof-local temporary data): finite generation of the adjoin uses algebraicity of the ambient perfect-closure extension.
  letI : Algebra.IsAlgebraic k (PerfectClosure k p) :=
    IsPurelyInseparable.isAlgebraic k (PerfectClosure k p)
  let root : k → PerfectClosure k p := fun a ↦
    Classical.choose (surjective_frobenius (PerfectClosure k p) p (algebraMap k (PerfectClosure k p) a))
  have hroot : ∀ a : k, root a ^ p = algebraMap k (PerfectClosure k p) a := by
    intro a
    exact Classical.choose_spec
      (surjective_frobenius (PerfectClosure k p) p (algebraMap k (PerfectClosure k p) a))
  let roots : Finset (PerfectClosure k p) := C.image root
  let k' : IntermediateField k (PerfectClosure k p) :=
    IntermediateField.adjoin k (roots : Set (PerfectClosure k p))
  refine ⟨k', inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  · rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem (F := k)
      (E := PerfectClosure k p) p]
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    refine ⟨1, ?_⟩
    refine ⟨a, ?_⟩
    simpa [pow_one] using (hroot a).symm
  · intro a ha
    refine ⟨⟨root a, IntermediateField.subset_adjoin (F := k)
      (S := (roots : Set (PerfectClosure k p))) ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · apply Subtype.val_injective
      simp [k', hroot a]

end FieldExtension
