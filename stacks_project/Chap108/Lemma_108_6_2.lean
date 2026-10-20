module

public import stacks_project.Chap108.Lemma_108_6_1_ProperOver
public import stacks_project.Chap108.Lemma_108_6_2_Projective

/-!
# Lemma 108.6.2

The Hilbert Quot algebraic space of finitely presented quotients on `P^n_B`
is proper over `B`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 108.6.2: for an algebraic space `B`, a finitely presented
`𝒪_X`-module `F` on `X = B × P^n_Z`, and Hilbert polynomial `P`, the algebraic
space `Quot^P` of quotients of `F` with Hilbert polynomial `P` with respect to
the pullback of `𝒪_{P^n}(1)` is proper over `B`. -/
@[stacks 0DPB]
theorem quotHilbert_projectiveOver_isProperOver {S : Scheme.{u}}
    (B : AlgebraicSpace S) (n : ℕ) (F : (ProjectiveSpace n B).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : ℤ → ℤ) :
    IsProperOver (quotHilbert_projectiveOver n B F P).toFunctor :=
  sorry

/-- Properness of `quotHilbert_projectiveOver` means some representing morphism
of algebraic spaces over `B` is proper. -/
theorem quotHilbert_projectiveOver_isProperOver_spec {S : Scheme.{u}}
    (B : AlgebraicSpace S) (n : ℕ) (F : (ProjectiveSpace n B).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : ℤ → ℤ) :
    IsProperOver (quotHilbert_projectiveOver n B F P).toFunctor ↔
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        Proper π ∧
          Nonempty
            ((quotHilbert_projectiveOver n B F P).toFunctor ≅ yonedaOver π) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
