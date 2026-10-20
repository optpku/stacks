module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LisseEtale
import StacksCheckRecall

/-!
# The lisse-étale site is not functorial
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 110.59.1: the lisse-étale site is not functorial, even for morphisms of
schemes. There exist schemes `S`, `T` and a morphism `f : T ⟶ S` such that
lisse-étale base change along `f` is continuous but its induced pullback on
sheaves does not preserve finite limits. -/
@[stacks 07BG] #check
  (AlgebraicGeometry.Scheme.exists_lisseEtaleSheafPullback_not_preservesFiniteLimits :
    ∃ (S T : Scheme.{u}) (f : T ⟶ S),
      ¬ CategoryTheory.Limits.PreservesFiniteLimits
        ((AlgebraicGeometry.Scheme.lisseEtalePullback f).sheafPullback (Type (u + 1))
          (AlgebraicGeometry.Scheme.lisseEtaleTopology S)
          (AlgebraicGeometry.Scheme.lisseEtaleTopology T)))
