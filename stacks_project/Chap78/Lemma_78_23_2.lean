module

public import stacks_project.Chap78.Lemma_78_23_2_Coequalizer
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

/- Lemma 78.23.2: Assumptions and notation as in Lemmas 78.20.2 and 78.20.3. The
2-commutative diagram of Lemma 78.20.3 is a 2-coequalizer in the following sense:
given a stack in groupoids `X` over `(Sch/S)_fppf`, a 1-morphism
`f : 𝒮_U ⟶ X`, and a 2-arrow `β : f ∘ s ⟶ f ∘ t` such that
`compWhisker G G.c.left β` equals the vertical composite of
`compWhisker G (pullback.snd G.s G.t).left β` then
`compWhisker G (pullback.fst G.s G.t).left β`, there exists a 1-morphism
`[U/R] ⟶ X` making the diagram `𝒮_R ⇉ 𝒮_U ⟶ [U/R]` against `f` 2-commute.
Here `pr₀` is `(pullback.fst G.s G.t).left`, `pr₁` is
`(pullback.snd G.s G.t).left`, `c` is `G.c.left`, left whiskering is
`CartesianBasedFunctor.precomp.map`, and 2-commutativity is a 1-morphism
`hom : [U/R] ⟶ X` with triangle `(atlas G).comp hom ≅ f`. -/
@[stacks 044U] #check
  (@existsCoequalizerLift :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (X : StackOver.Groupoids (Scheme.fppfTopology.over S))
      (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
      (β : (stackInSets.map G.s.left).comp f ⟶
        (stackInSets.map G.t.left).comp f),
      IsCoequalizerCocycle G f β → Nonempty (CoequalizerLift G X f β))
