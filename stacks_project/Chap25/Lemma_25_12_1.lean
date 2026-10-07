module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Splitting
import StacksCheckRecall

/-!
# Splitting criteria for simplicial semi-representable families

The componentwise and splitting APIs are owned by the reusable formal-coproduct layer.
-/

open CategoryTheory

/- Lemma 25.12.1 (1): a truncated simplicial semi-representable family is split exactly when
epimorphisms of truncated simplices induce isomorphisms on every component. -/
@[stacks 0DAU "truncated split iff epimorphisms"]
#check @SimplicialObject.Truncated.Componentwise.isSplit_iff_epis

/- Lemma 25.12.1 (2): for a truncated simplicial semi-representable family, it is enough to test
the componentwise isomorphism condition on the standard degeneracy operators. -/
@[stacks 0DAU "truncated epimorphisms iff degeneracies"]
#check @SimplicialObject.Truncated.Componentwise.epis_iff_degeneracies

/- Lemma 25.12.1 (3): a simplicial semi-representable family is split exactly when epimorphisms
of simplices induce isomorphisms on every component. -/
@[stacks 0DAU "simplicial split iff epimorphisms"]
#check @SimplicialObject.Componentwise.isSplit_iff_epis

/- Lemma 25.12.1 (4): for a simplicial semi-representable family, it is enough to test the
componentwise isomorphism condition on the standard degeneracy operators. -/
@[stacks 0DAU "simplicial epimorphisms iff degeneracies"]
#check @SimplicialObject.Componentwise.epis_iff_degeneracies

-- Fine-grained component and direct split-versus-degeneracy APIs.
#check @Limits.FormalCoproduct.componentIndex
#check @Limits.FormalCoproduct.componentMap
#check @Limits.FormalCoproduct.Componentwise.IsoOnEpis
#check @SimplicialObject.Truncated.Componentwise.isSplit_iff_degeneracies
#check @SimplicialObject.Componentwise.isSplit_iff_degeneracies
