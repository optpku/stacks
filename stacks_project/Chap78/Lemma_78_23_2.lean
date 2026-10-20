module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Coequalizer
import StacksCheckRecall

universe u uX vX

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

/- Lemma 78.23.2: Assumptions and notation as in Lemmas 78.20.2 and 78.20.3. The
2-commutative diagram of Lemma 78.20.3 is a 2-coequalizer in the following sense:
given a stack in groupoids `X` over `(Sch/S)_fppf`, a 1-morphism
`f : 𝒮_U ⟶ X`, and a 2-arrow `β : f ∘ s ⟶ f ∘ t` satisfying the cocycle
`β ★ id_c = (β ★ id_pr₀) ∘ (β ★ id_pr₁)`, there exists a 1-morphism
`[U/R] ⟶ X` making the diagram `𝒮_R ⇉ 𝒮_U ⟶ [U/R]` against `f` 2-commute.
Here `pr₀` is `(pullback.fst G.s G.t).left`, `pr₁` is
`(pullback.snd G.s G.t).left`, `c` is `G.c.left`, and left whiskering is
`CartesianBasedFunctor.precomp.map`. The factorization has a triangle
`(fppfAtlas G).comp hom ≅ f` compatible with `β` and the canonical atlas cell. -/
@[stacks 044U] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.existsCoequalizerLift :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S))
      (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
      (β : (stackInSets.map G.s.left).comp f ⟶
        (stackInSets.map G.t.left).comp f),
      IsCoequalizerCocycle G f β →
        ∃ hom : CartesianBasedFunctor (fppfQuotientStack G).p X.p,
          ∃ triangle : (fppfAtlas G).comp hom ≅ f,
            IsCoequalizerCompat G f β hom triangle)
