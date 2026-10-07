module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_9_1_Localizing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 96.9.1 (1): let `p : X ⟶ (Sch/S)_fppf` be a category fibred in groupoids,
and let `x` lie over `U = (X.p.obj x).left`. Then `p` induces an equivalence of
categories `Over x ≌ Over U`. -/
@[stacks 06W0]
#check fun {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total) ↦
  Functor.overPostScheme.isEquivalence X.p x

/- Lemma 96.9.1 (2): for `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, the same
functor is an equivalence of sites `X_τ / x ⟶ (Sch/U)_τ`. -/
@[stacks 06W0]
#check fun {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology)
    (x : X.total) ↦ Functor.overPostScheme.isDenseSubsite X.p x τ

#check fun {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total) ↦
  Functor.overPostScheme X.p x

#check Functor.overPostScheme.covering_iff
