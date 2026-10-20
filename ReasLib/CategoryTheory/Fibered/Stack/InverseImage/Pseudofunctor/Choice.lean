module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Direct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global choices for inverse-image pseudofunctoriality

An inverse-image stack and the inverse to its stackification precomposition functor are not
canonical data.  This file collects those choices for every stack and every Hom category, while
leaving bicategorical identity and composition coherence to a separate owner.
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

variable {u : C ⥤ D}

set_option linter.checkUnivs false in
/-- Explicit global data needed before inverse image can act pseudofunctorially on stacks.

The object field chooses an inverse-image stack for every source stack, while `quasiInverse`
supplies the genuinely noncanonical inverse functor on each Hom category. Pushforward inversion
is proposition-valued and is supplied canonically rather than stored as choice data. -/
@[stacks 04WS "global inverse-image pseudofunctor choice"]
structure PseudofunctorChoice (u : C ⥤ D) where
  /-- The chosen inverse-image stack of every stack over `(C, J)`. -/
  obj (S : StackOver.{uC, vC,
    max w₀ (max uC (max uD (max vC vD))),
    max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    StackOver.InverseImage K u S
  /-- The chosen inverse to precomposition with the source stackification comparison on each
  Hom category. -/
  quasiInverse (S S' : StackOver.{uC, vC,
    max w₀ (max uC (max uD (max vC vD))),
    max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    Functor.QuasiInverse
      (StackOver.Hom.precomp (obj S').target (obj S).comparisonHom)

attribute [stacks 04WS "inverse-image pseudofunctor object choice"]
  StackOver.InverseImage.PseudofunctorChoice.obj
attribute [stacks 04WS "inverse-image Hom quasi-inverse choice"]
  StackOver.InverseImage.PseudofunctorChoice.quasiInverse

/-- Complete the Hom-level inversion family with the endpoint choices already owned by the two
selected inverse-image objects.  This bridge only assembles proposition-valued fields; it does
not need the finite-limit hypotheses used later to construct the Hom functor. -/
@[stacks 04WS "canonical inverse-image pushforward proof family"]
def PseudofunctorChoice.pushforwardChoice
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver :=
  (FiberedCategoryOver.Pushforward.MapInversionChoice.canonical u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver).withEndpoints
    (h.obj S).sourceChoice (h.obj S').sourceChoice

/-- The source projection in the selected pushforward choice is the source projection of the
chosen inverse-image stack. -/
@[simp, stacks 04WS "chosen inverse-image pushforward source endpoint"]
theorem PseudofunctorChoice.pushforwardChoice.source
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁} (J := J) (K := K) u)
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    (h.pushforwardChoice S S').source = (h.obj S).sourceChoice := sorry

/-- The target projection in the selected pushforward choice is the target projection of the
chosen inverse-image stack. -/
@[simp, stacks 04WS "chosen inverse-image pushforward target endpoint"]
theorem PseudofunctorChoice.pushforwardChoice.target
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁} (J := J) (K := K) u)
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    (h.pushforwardChoice S S').target = (h.obj S').sourceChoice := sorry

/-- The inversion proof in the selected inverse-image pushforward choice is the canonical
source-level proof; endpoint choices do not alter it. -/
@[simp, stacks 04WS "chosen inverse-image pushforward inversion readout"]
theorem PseudofunctorChoice.pushforwardChoice.inverts
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁} (J := J) (K := K) u)
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J)
    (F : S.toFiberedCategoryOver ⟶ S'.toFiberedCategoryOver) :
    (h.pushforwardChoice S S').inverts F =
      (FiberedCategoryOver.Pushforward.MapInversionChoice.canonical u
        S.toFiberedCategoryOver S'.toFiberedCategoryOver).inverts F := sorry

/-- The Hom functor selected by a global inverse-image choice. -/
@[stacks 04WS "chosen inverse-image Hom functor"]
noncomputable def PseudofunctorChoice.mapFunctor
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    (S ⟶ S') ⥤ ((h.obj S).target ⟶ (h.obj S').target) :=
  mapHom (h.obj S) (h.obj S')
    (h.pushforwardChoice S S')
    (h.quasiInverse S S')

namespace PseudofunctorChoice.mapFunctor

/-- The object action of the selected Hom functor is the direct inverse-image construction with
the canonical pushforward inversion proof family. -/
@[simp, stacks 04WS "chosen inverse-image Hom object computation"]
theorem obj
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ S') :
    (h.mapFunctor S S').obj F =
      (mapHom (h.obj S) (h.obj S') (h.pushforwardChoice S S')
        (h.quasiInverse S S')).obj F := sorry

/-- The morphism action of the selected Hom functor is the direct inverse-image action on the
supplied stack `2`-cell. -/
@[simp, stacks 04WS "chosen inverse-image Hom map computation"]
theorem map
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    {F G : S ⟶ S'} (eta : F ⟶ G) :
    (h.mapFunctor S S').map eta =
      (mapHom (h.obj S) (h.obj S') (h.pushforwardChoice S S')
        (h.quasiInverse S S')).map eta := sorry

end PseudofunctorChoice.mapFunctor

/-- The prelax core determined by the object and Hom-category parts of a global inverse-image
choice. -/
@[stacks 04WS "chosen inverse-image prelax core"]
noncomputable def PseudofunctorChoice.prelax
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PrelaxFunctor
      (StackOver.{uC, vC,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} J)
      (StackOver.{uD, vD,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} K) :=
  PrelaxFunctor.mkOfHomFunctors (fun S ↦ (h.obj S).target)
    h.mapFunctor

namespace PseudofunctorChoice.prelax

/-- The selected prelax functor sends a stack to the target of its chosen inverse-image stack. -/
@[simp, stacks 04WS "chosen inverse-image prelax object computation"]
theorem obj
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (S : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    h.prelax.obj S = (h.obj S).target := sorry

/-- The selected prelax functor uses the chosen Hom functor on each `1`-cell. -/
@[simp, stacks 04WS "chosen inverse-image prelax morphism computation"]
theorem map
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ S') :
    h.prelax.map F = (h.mapFunctor S S').obj F := sorry

/-- The selected prelax functor uses the morphism action of the chosen Hom functor on
`2`-cells. -/
@[simp, stacks 04WS "chosen inverse-image prelax two-cell computation"]
theorem map₂
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    {F G : S ⟶ S'} (eta : F ⟶ G) :
    h.prelax.map₂ eta = (h.mapFunctor S S').map eta := sorry

/-- The Hom functor exposed by the selected prelax core is the chosen inverse-image Hom
functor. -/
@[simp, stacks 04WS "chosen inverse-image prelax Hom computation"]
theorem mapFunctor
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    h.prelax.mapFunctor S S' = h.mapFunctor S S' := sorry

end PseudofunctorChoice.prelax

-- Data audit: every inverse-image stack and Hom quasi-inverse is an explicit field. The removed
-- Hom inversion field was proposition-valued and is supplied by the canonical localization API.

end StackOver.InverseImage

end CategoryTheory
