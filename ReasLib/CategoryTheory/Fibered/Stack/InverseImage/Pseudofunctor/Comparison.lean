module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Components
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackification comparison for the inverse-image pseudofunctor

The selected inverse-image map becomes the pushed-forward source map after postcomposition with
the target stackification comparison.  This file exposes that natural isomorphism directly at the
global-choice and pseudofunctor layers.
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
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- The Hom-level stackification comparison selected by a global inverse-image choice. -/
@[stacks 04WS "stackification comparison for a global inverse-image choice"]
noncomputable def PseudofunctorChoice.comparisonIso
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    h.mapFunctor S S' ⋙
        StackOver.Hom.precomp (h.obj S').target (h.obj S).comparisonHom ≅
      StackOver.Pushforward.mapFunctor u
          (h.pushforwardChoice S S') ⋙
        Bicategory.postcomp
          (FiberedCategoryOver.pushforward u S.toFiberedCategoryOver
            (h.pushforwardChoice S S').source)
          (h.obj S').comparisonHom :=
  mapHom.comparisonIso (h.obj S) (h.obj S')
    (h.pushforwardChoice S S')
    (h.quasiInverse S S')

/-- The forward component of the global-choice comparison is the selected quasi-inverse
counit. -/
@[simp, stacks 04WS "chosen inverse-image comparison forward component"]
theorem PseudofunctorChoice.comparisonIso.hom.app
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ S') :
    (h.comparisonIso S S').hom.app F =
      (h.quasiInverse S S').counitIso.hom.app
        ((StackOver.Pushforward.mapFunctor u
          (h.pushforwardChoice S S')).obj F ≫
            (h.obj S').comparisonHom) := sorry

/-- The inverse component of the global-choice comparison is the inverse selected
quasi-inverse counit. -/
@[simp, stacks 04WS "chosen inverse-image comparison inverse component"]
theorem PseudofunctorChoice.comparisonIso.inv.app
    (h : PseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u)
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ S') :
    (h.comparisonIso S S').inv.app F =
      (h.quasiInverse S S').counitIso.inv.app
        ((StackOver.Pushforward.mapFunctor u
          (h.pushforwardChoice S S')).obj F ≫
            (h.obj S').comparisonHom) := sorry

/-- The stackification comparison for the Hom action of the selected inverse-image
pseudofunctor. -/
@[stacks 04WS "stackification comparison for the inverse-image pseudofunctor"]
noncomputable def pseudofunctor.comparisonIso
    (h : CoherentPseudofunctorChoice (J := J) (K := K) u)
    (S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    (pseudofunctor u h).mapFunctor S S' ⋙
        StackOver.Hom.precomp (h.toChoice.obj S').target
          (h.toChoice.obj S).comparisonHom ≅
      StackOver.Pushforward.mapFunctor u
          (h.toChoice.pushforwardChoice S S') ⋙
        Bicategory.postcomp
          (FiberedCategoryOver.pushforward u S.toFiberedCategoryOver
            (h.toChoice.pushforwardChoice S S').source)
          (h.toChoice.obj S').comparisonHom :=
  h.toChoice.comparisonIso S S'

/-- The forward component of the pseudofunctor stackification comparison. -/
@[simp, stacks 04WS "inverse-image pseudofunctor comparison forward component"]
theorem pseudofunctor.comparisonIso.hom.app
    (h : CoherentPseudofunctorChoice (J := J) (K := K) u)
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ S') :
    (pseudofunctor.comparisonIso h S S').hom.app F =
      (h.toChoice.quasiInverse S S').counitIso.hom.app
        ((StackOver.Pushforward.mapFunctor u
          (h.toChoice.pushforwardChoice S S')).obj F ≫
            (h.toChoice.obj S').comparisonHom) := sorry

/-- The inverse component of the pseudofunctor stackification comparison. -/
@[simp, stacks 04WS "inverse-image pseudofunctor comparison inverse component"]
theorem pseudofunctor.comparisonIso.inv.app
    (h : CoherentPseudofunctorChoice (J := J) (K := K) u)
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (F : S ⟶ S') :
    (pseudofunctor.comparisonIso h S S').inv.app F =
      (h.toChoice.quasiInverse S S').counitIso.inv.app
        ((StackOver.Pushforward.mapFunctor u
          (h.toChoice.pushforwardChoice S S')).obj F ≫
            (h.toChoice.obj S').comparisonHom) := sorry

end StackOver.InverseImage

end CategoryTheory
