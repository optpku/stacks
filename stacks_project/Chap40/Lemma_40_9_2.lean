module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.MorphismProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]

/- Lemma 40.9.2: If the slicing source map has a morphism property stable under base
change, then both structure maps of the restricted groupoid scheme have that property. -/
@[stacks 04MV] #check
  (AlgebraicGeometry.GroupoidScheme.pullback_source_target_mem G g P :
    P ((pullback.snd g G.t ≫ G.s).left) →
      P ((G.pullback g).s.left) ∧ P ((G.pullback g).t.left))

end AlgebraicGeometry.GroupoidScheme
