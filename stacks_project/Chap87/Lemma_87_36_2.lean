module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal
public import stacks_project.Chap87.Lemma_87_36_1

/-!
# Lemma 87.36.2

A directed colimit of formal algebraic spaces along closed immersions
inducing isomorphisms on reductions is again a formal algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsFormalAlgebraicSpace

open IsAffineFormalAlgebraicSpace (isRelativeThickening)

/-- Lemma 87.36.2: Let `S` be a scheme. Suppose given a directed set `Λ` and a
system of formal algebraic spaces `(X_λ, f_λμ)` over `Λ` where each
`f_λμ : X_λ ⟶ X_μ` is a closed immersion inducing an isomorphism
`X_λ,red ⟶ X_μ,red`. Then `X = colim_λ X_λ` is a formal algebraic
space over `S`. Transitions are the section's representable thickenings
`isRelativeThickening`, equivalently closed immersions inducing isomorphisms
on reductions. -/
@[stacks 0GVN]
theorem of_directedColimit {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_formal : ∀ i : Λ, IsFormalAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (hij : i ≤ j),
      isRelativeThickening (F.map (homOfLE hij)))
    (c : Cocone F) (hc : IsColimit c) :
    IsFormalAlgebraicSpace c.pt :=
  sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
