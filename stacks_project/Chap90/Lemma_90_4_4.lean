module

public import stacks_project.Chap90.Lemma_90_4_4_TensorCompletion

/-!
# Coproducts of pairs in the completed base category
-/

@[expose] public section

open CategoryTheory Limits CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.4.4: the completed base category Ĉ_Λ = CompleteLocalAlgCat Λ k admits
coproducts of pairs of objects. -/
@[stacks 06H1]
instance hasBinaryCoproducts : HasBinaryCoproducts (CompleteLocalAlgCat Λ k) :=
  hasBinaryCoproducts_of_hasColimit_pair (CompleteLocalAlgCat Λ k)

end CompleteLocalAlgCat
