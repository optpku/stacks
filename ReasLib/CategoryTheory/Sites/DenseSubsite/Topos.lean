module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# The morphism of topoi presented by a dense subsite

A dense-subsite functor presents an equivalence of sheaf categories.  In the direction induced by
the comparison functor, its inverse image is continuous sheaf pushforward and its direct image is
the canonical quasi-inverse supplied by `sheafEquiv`.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The equivalence of topoi induced by a dense-subsite functor, oriented from `Sh(J)` to
`Sh(K)`. -/
@[stacks 03CR "dense comparison"]
noncomputable def morphismOfTopoiIn (G : C ⥤ D) [G.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) (Type w)] :
    MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, w} K J where
  inverseImageFunctor :=
    LeftExactFunctor.of (G.sheafPushforwardContinuous (Type w) J K)
  pushforward := (sheafEquiv J K G (Type w)).functor
  adjunction := (sheafEquiv J K G (Type w)).symm.toAdjunction

-- All non-Prop data is the canonical dense-subsite equivalence and its adjunction.

end CategoryTheory.Functor.IsDenseSubsite
