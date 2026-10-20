module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Pullback on small pro-étale sites

The small pro-étale site is a morphism-property full subcategory. This leaf
gives its base-change functor through Mathlib's generic over-category
pullback construction.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- Base change along `f` on the small pro-étale sites of schemes. -/
noncomputable abbrev smallProetalePullback (f : T ⟶ S) :
    S.ProEt ⥤ T.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Base change is continuous for the small pro-étale topologies. -/
instance smallProetalePullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (smallProetalePullback f)
      (ProEt.topology S) (ProEt.topology T) := sorry

end AlgebraicGeometry.Scheme
