module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.Stalk

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.42.2: let `f : X ⟶ S` be a finite type morphism of schemes and `x : X`. If the
induced stalk map is an isomorphism, `S` is reduced, and `S` has finitely many irreducible
components, then `f` restricts to an open immersion on an open neighborhood of `x`. -/
@[stacks 09NH] #check
  (AlgebraicGeometry.Scheme.Hom.exists_openImmersion_neighborhood_of_stalkMap_isIso :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsReduced S]
      [Finite (irreducibleComponents S)] (x : X) [IsIso (f.stalkMap x)],
      ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f))
