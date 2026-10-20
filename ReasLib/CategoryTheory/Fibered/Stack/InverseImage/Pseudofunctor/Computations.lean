module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the inverse-image pseudofunctor

These lemmas expose the selected inverse-image object, Hom functor, `1`-cell and `2`-cell actions,
and the two structural comparisons without unfolding the pseudofunctor package.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable (h : CoherentPseudofunctorChoice (J := J) (K := K) u)

/-- The object action is the target of the selected inverse-image stack. -/
@[simp, stacks 04WS "inverse-image pseudofunctor object computation"]
theorem pseudofunctor.obj
    (S : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    (pseudofunctor u h).obj S = (h.toChoice.obj S).target := sorry

/-- On each Hom category, the inverse-image pseudofunctor is the functor selected by the global
choice. -/
@[simp, stacks 04WS "inverse-image pseudofunctor Hom computation"]
theorem pseudofunctor.mapFunctor
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    (pseudofunctor u h).mapFunctor S S' =
      h.toChoice.mapFunctor S S' := sorry

/-- The `1`-cell action is direct inverse image using the selected pushforward and
stackification-lift choices. -/
@[simp, stacks 04WS "inverse-image pseudofunctor morphism computation"]
theorem pseudofunctor.map
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ S') :
    (pseudofunctor u h).map F =
      (h.toChoice.mapFunctor S S').obj F := sorry

/-- The `2`-cell action is the morphism action of the selected direct inverse-image Hom
functor. -/
@[simp, stacks 04WS "inverse-image pseudofunctor two-cell computation"]
theorem pseudofunctor.map₂
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    {F G : S ⟶ S'} (eta : F ⟶ G) :
    (pseudofunctor u h).map₂ eta =
      (h.toChoice.mapFunctor S S').map eta := sorry

/-- The identity comparison is the one carried by the coherent global choice. -/
@[simp, stacks 04WS "inverse-image pseudofunctor identity comparison"]
theorem pseudofunctor.mapId
    (S : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    (pseudofunctor u h).mapId S = h.mapId S := sorry

/-- The composition comparison is the one carried by the coherent global choice. -/
@[simp, stacks 04WS "inverse-image pseudofunctor composition comparison"]
theorem pseudofunctor.mapComp
    {S T U : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ T) (G : T ⟶ U) :
    (pseudofunctor u h).mapComp F G = h.mapComp F G := sorry

end StackOver.InverseImage

end CategoryTheory
