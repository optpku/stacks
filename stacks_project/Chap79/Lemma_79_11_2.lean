module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap79.Lemma_79_11_2_SelfProduct

/-!
# Factoring maps out of a self-product of the projective line

A morphism of algebraic spaces over a field from `(P¹_k)^n` to a separated
finite-type algebraic space factors as a coordinate projection followed by a
finite morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 79.11.2: Let `k` be a field. Let `n ≥ 1` and let `(P¹_k)^n` be the
`n`-fold self-product over `Spec k`. Let `f : (P¹_k)^n ⟶ Z` be a morphism of
algebraic spaces over `k`. If `Z` is separated of finite type over `k`, then
`f` factors as a coordinate projection `(P¹_k)^n ⟶ (P¹_k)^m` followed by a
finite morphism `(P¹_k)^m ⟶ Z`.

The projection is `projectiveLineSelfProductπ k e` for an embedding
`e : Fin m ↪ Fin n` selecting a subset of the factors. -/
@[stacks 0AEM]
theorem exists_isFinite_factor_of_projectiveLineSelfProduct
    {k : Type u} [Field k] {n : ℕ} (hn : 1 ≤ n)
    {Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Separated (toBase Z)] [FiniteType (toBase Z)]
    (f : projectiveLineSelfProduct k n ⟶ Z) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin n) (g : projectiveLineSelfProduct k m ⟶ Z),
      IsFinite g ∧ projectiveLineSelfProductπ k (e : Fin m → Fin n) ≫ g = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
