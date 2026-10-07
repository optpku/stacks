module

public import stacks_project.Chap03.Lemma_3_9_4_Size
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.4: the Stacks size of an affine scheme `S` equals `#(Γ(S, ⊤)) ⊔ ℵ₀`. -/
@[stacks 000P]
theorem size_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    S.size = #(Γ(S, ⊤)) ⊔ ℵ₀ := sorry

/-- The Stacks size of `Spec R` equals `#R ⊔ ℵ₀`. -/
theorem size_Spec (R : CommRingCat.{u}) : (Spec R).size = #R ⊔ ℵ₀ := sorry

end AlgebraicGeometry.Scheme
