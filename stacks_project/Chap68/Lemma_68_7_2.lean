module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Specialization

/-!
# No specializations in étale fibres over a locally Noetherian algebraic space

An étale morphism from a scheme to a locally Noetherian algebraic space has no
nontrivial specializations among scheme points that map to the same point of the
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.7.2: Let `S` be a scheme, `X` a locally Noetherian algebraic space over `S`,
and `φ : ofOver U ⟶ X` an étale morphism from a scheme. If `u` and `u'` map to the
same point of `X` and `u'` specializes to `u`, then `u = u'`. -/
@[stacks 0H1Q] #check
  (AlgebraicGeometry.AlgebraicSpace.eq_of_specializes_of_mapOfOver_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
      {u u' : U.left} {x : Points X},
      Points.mapOfOver φ u = x → Points.mapOfOver φ u' = x →
      Specializes u' u → u = u')

end AlgebraicGeometry.AlgebraicSpace
