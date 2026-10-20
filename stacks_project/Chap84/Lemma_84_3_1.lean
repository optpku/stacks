module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.SchemeComparison

/-!
# Lemma 84.3.1

The inclusion of big sites `(Sch/S)_τ ⟶ (Spaces/S)_τ` along `ofOverFunctor S`
is special cocontinuous for `τ ∈ {étale, fppf, ph}`, and therefore identifies
the corresponding sheaf topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 84.3.1: the canonical inclusion is special cocontinuous for the étale,
fppf, and ph topologies and identifies the corresponding sheaf topoi. The six
checks record these three comparisons and their direct-image equivalences. -/
@[stacks 0DFV] #check
  (AlgebraicGeometry.AlgebraicSpace.ofOverFunctor_isSpecialCocontinuous_etale :
    ∀ S : Scheme.{u},
      (ofOverFunctor S).IsSpecialCocontinuous (Scheme.etaleTopology.over S) etaleTopology)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverFunctor_directImage_isEquivalence_etale :
  ∀ S : Scheme.{u},
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.etaleTopology.over S) etaleTopology).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverFunctor_isSpecialCocontinuous_fppf :
  ∀ S : Scheme.{u},
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.fppfTopology.over S) (fppfTopology S))

#check (AlgebraicGeometry.AlgebraicSpace.ofOverFunctor_directImage_isEquivalence_fppf :
  ∀ S : Scheme.{u},
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.fppfTopology.over S) (fppfTopology S)).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverFunctor_isSpecialCocontinuous_ph :
  ∀ S : Scheme.{u},
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.bigPhSite S) (phTopology S))

#check (AlgebraicGeometry.AlgebraicSpace.ofOverFunctor_directImage_isEquivalence_ph :
  ∀ S : Scheme.{u},
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.bigPhSite S) (phTopology S)).IsEquivalence)
