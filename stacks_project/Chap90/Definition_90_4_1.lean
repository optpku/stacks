module

public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Definition 90.4.1: Ĉ_Λ is the category of pairs (R, φ) where R is a Noetherian
complete local Λ-algebra and φ : ResidueField R ≃ₐ[Λ] k is a Λ-algebra isomorphism;
morphisms (S, ψ) ⟶ (R, φ) are local Λ-algebra maps f : S → R satisfying
φ.comp (ResidueField.mapAlgHom f) = ψ. -/
@[stacks 06GW]
#check (CompleteLocalAlgCat Λ k)

variable (R S : CompleteLocalAlgCat Λ k)

#check (CompleteLocalAlgCat.Hom R S)

#check (inferInstance : Category.{u} (CompleteLocalAlgCat Λ k))
