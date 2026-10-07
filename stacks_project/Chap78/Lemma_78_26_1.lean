module

public import stacks_project.Chap78.Lemma_78_26_1_Comparison
public import stacks_project.Chap78.Lemma_78_26_1_Presentation
import StacksCheckRecall

/-!
# Lemma 78.26.1

The stabilizer groupoid `(G, R', s', t', c')` presents the inertia stack of `[U/R]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

universe u

/- Lemma 78.26.1 (1): the stabilizer `G/U` of a groupoid `(U, R, s, t, c)` in algebraic
spaces over `B` determines a groupoid `(G, R', s', t', c')` over `B`, with
`R' = R ×_{s, U} G`, source `(r, g) ↦ g`, target `(r, g) ↦ c(r, c(g, i(r)))`, and
composition `((later, g_later), (earlier, g_earlier)) ↦ (c(later, earlier), g_earlier)`. -/
@[stacks 06PB] #check
  (@inertiaPresentation :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
      GroupoidAlgebraicSpace B → GroupoidAlgebraicSpace B)

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 78.26.1 (2): the quotient stack of the inertia presentation is the inertia
stack of `[U/R]`, via the canonical cartesian `1`-morphism
`I_{[U/R]} ⟶ [G/R']`. -/
@[stacks 06PB, instance]
instance inertia_quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaComparison G).toBasedFunctor.IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
