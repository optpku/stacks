module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Comparison

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 40.9.3: For two successive restrictions of a groupoid scheme, the canonical
comparison diagram commutes and both squares are cartesian. -/
@[stacks 04MW] #check
  (AlgebraicGeometry.GroupoidScheme.iteratedRestrictionDiagram :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {U' U'' : Over S}
      (g : U' ⟶ G.U) (g' : U'' ⟶ U'),
      IsPullback (restrictionComparison G g g')
          (pullback.fst (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s))
          (pullback.snd g' (G.pullback g).t ≫ (G.pullback g).s)
          (pullback.fst g G.t) ∧
        IsPullback
          (pullback.snd (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s))
          (pullback.fst (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s))
          (pullback.snd (g' ≫ g) G.t ≫ G.s)
          (pullback.snd g G.t ≫ G.s))

end AlgebraicGeometry.GroupoidScheme
