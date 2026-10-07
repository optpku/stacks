module

public import stacks_project.Chap99.Lemma_99_5_11_Versal

/-!
# Lemma 99.5.11

In Situation 99.5.1, if `S` is locally Noetherian, `S = B`, and `f : X ⟶ B` is
flat, then `𝒳 = Coh_{X/B}` satisfies openness of versality in the sense of
Artin's Axioms, Definition 98.13.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- Lemma 99.5.11: in Situation 99.5.1 assume that `S` is a locally Noetherian
scheme, `S = B`, and `f : X ⟶ B` is flat. Let `𝒳 = Coh_{X/B}`. Then `𝒳`
satisfies openness of versality in the sense of Artin's Axioms, Definition
98.13.1: if `U ⟶ S` is locally of finite type, `x` is an object of `𝒳` over
`U`, and `u0 ∈ U` is a finite type point at which `x` is versal, then there is
an open neighbourhood `u0 ∈ U' ⊂ U` such that `x` is versal at every finite
type point of `U'`. -/
@[stacks 08WA]
theorem opennessOfVersality {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [FinitePresentation f] [Flat f] {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f) (hx : (p f).obj x = Over.mk hU)
    (u0 : U) : IsFiniteTypePoint u0 → IsVersalAt f hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt f hU x hx u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
