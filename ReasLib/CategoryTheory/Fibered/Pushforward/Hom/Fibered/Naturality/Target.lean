/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Construction
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Pullback.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Target naturality of the pushforward-pullback Hom functor

This leaf records compatibility with postcomposition in the target fibered category. Its
objectwise comparison is explicit identity data; equality transport is retained only as a
propositional readout.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

namespace Hom

variable {X : FiberedCategoryOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
variable {hX : ProjectionChoice u X}
variable {Y Z : FiberedCategoryOver.{uD, vD,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}

/-- Precomposing with the pushforward unit commutes with postcomposition after applying the
canonical pullback map to the target morphism. -/
@[simp, stacks 04WI "bundled Hom target naturality"]
theorem obj.postcomp
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z) :
    obj u (H ≫ G) = obj u H ≫ Pullback.mapCanonical u G := sorry

/-- Compatibility of the two identity arrows defining the target-postcomposition component in
the categorical pullback. -/
@[stacks 04WI "bundled Hom target comparison compatibility"]
theorem postcompApp.compatibility
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    u.map (Iso.refl _).hom ≫
        ((FiberedCategoryOver.toFunctor
          (obj u H ≫ Pullback.mapCanonical u G)).obj x).iso.hom =
      ((FiberedCategoryOver.toFunctor (obj u (H ≫ G))).obj x).iso.hom ≫
        Z.p.map (Iso.refl _).hom := sorry

/-- The explicit pointwise target-postcomposition isomorphism in the categorical pullback. Its
two object components, in both directions, are identities; only compatibility with the stored
structural isomorphisms is propositional. -/
@[stacks 04WI "bundled Hom target comparison component"]
noncomputable def postcompApp
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (FiberedCategoryOver.toFunctor (obj u (H ≫ G))).obj x ≅
      (FiberedCategoryOver.toFunctor
        (obj u H ≫ Pullback.mapCanonical u G)).obj x :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    (postcompApp.compatibility u H G x)

/-- The first component of the forward pointwise target comparison is the identity. -/
@[simp, stacks 04WI "bundled Hom target forward first component"]
theorem postcompApp.hom.fst
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (postcompApp u H G x).hom.fst = 𝟙 _ := sorry

/-- The second component of the forward pointwise target comparison is the identity. -/
@[simp, stacks 04WI "bundled Hom target forward second component"]
theorem postcompApp.hom.snd
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (postcompApp u H G x).hom.snd = 𝟙 _ := sorry

/-- The first component of the inverse pointwise target comparison is the identity. -/
@[simp, stacks 04WI "bundled Hom target inverse first component"]
theorem postcompApp.inv.fst
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (postcompApp u H G x).inv.fst = 𝟙 _ := sorry

/-- The second component of the inverse pointwise target comparison is the identity. -/
@[simp, stacks 04WI "bundled Hom target inverse second component"]
theorem postcompApp.inv.snd
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (postcompApp u H G x).inv.snd = 𝟙 _ := sorry

/-- The pointwise target-postcomposition isomorphisms are natural in the source object. -/
@[stacks 04WI "bundled Hom target comparison naturality"]
theorem postcompApp.naturality
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    {x y : X.total} (f : x ⟶ y) :
    (FiberedCategoryOver.toFunctor (obj u (H ≫ G))).map f ≫
        (postcompApp u H G y).hom =
      (postcompApp u H G x).hom ≫
        (FiberedCategoryOver.toFunctor
          (obj u H ≫ Pullback.mapCanonical u G)).map f := sorry

/-- The explicit natural isomorphism on total categories underlying target postcomposition. -/
@[stacks 04WI "bundled Hom target total isomorphism"]
noncomputable def postcompNatIso
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.toFunctor (obj u (H ≫ G)) ≅
      FiberedCategoryOver.toFunctor
        (obj u H ≫ Pullback.mapCanonical u G) :=
  NatIso.ofComponents (postcompApp u H G)
    (fun f ↦ postcompApp.naturality u H G f)

/-- The forward total-category target comparison lies over the identity of each base object. -/
@[stacks 04WI "bundled Hom target comparison lift"]
theorem postcompNatIso.isHomLift
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (FiberedCategoryOver.pullback u Z).p.IsHomLift (𝟙 (X.p.obj x))
      ((postcompNatIso u H G).hom.app x) := sorry

/-- The explicit based-functor isomorphism underlying target postcomposition. -/
@[stacks 04WI "bundled Hom target based isomorphism"]
noncomputable def postcompBasedIso
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.toBasedFunctor (obj u (H ≫ G)) ≅
      FiberedCategoryOver.toBasedFunctor
        (obj u H ≫ Pullback.mapCanonical u G) :=
  BasedNatIso.mkNatIso (postcompNatIso u H G)
    (postcompNatIso.isHomLift u H G)

/-- The explicit target-postcomposition comparison between morphisms of fibred categories. Its
non-Prop data descend from the identity components of `postcompApp`. -/
@[stacks 04WI "bundled Hom target comparison isomorphism"]
noncomputable def postcompIso
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z) :
    obj u (H ≫ G) ≅ obj u H ≫ Pullback.mapCanonical u G :=
  FiberedCategoryOver.BasedFunctorIso.lift (postcompBasedIso u H G)

/-- The total-category component of the forward target comparison is `postcompApp.hom`. -/
@[simp, stacks 04WI "bundled Hom target comparison forward component"]
theorem postcompIso.hom.app
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (FiberedCategoryOver.toNatTrans (postcompIso u H G).hom).app x =
      (postcompApp u H G x).hom := sorry

/-- The total-category component of the inverse target comparison is `postcompApp.inv`. -/
@[simp, stacks 04WI "bundled Hom target comparison inverse component"]
theorem postcompIso.inv.app
    (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) (G : Y ⟶ Z)
    (x : X.total) :
    (FiberedCategoryOver.toNatTrans (postcompIso u H G).inv).app x =
      (postcompApp u H G x).inv := sorry

/-- The explicit target-postcomposition components are natural in vertical transformations out
of the pushforward. -/
@[stacks 04WI "bundled Hom target comparison naturality"]
theorem map.postcomp
    {H K : FiberedCategoryOver.pushforward u X hX ⟶ Y}
    (τ : H ⟶ K) (G : Y ⟶ Z) :
    map u (τ ▷ G) ≫ (postcompIso u K G).hom =
      (postcompIso u H G).hom ≫
        map u τ ▷ Pullback.mapCanonical u G := sorry

end Hom

namespace homFunctor

variable {X : FiberedCategoryOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
variable {Y Z : FiberedCategoryOver.{uD, vD,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}

/-- Target-variable naturality of the pushforward-pullback Hom functor: postcomposing before
the Hom comparison agrees canonically with postcomposing by the pulled-back target map after
the comparison. -/
@[stacks 04WI "Hom functor target naturality isomorphism"]
noncomputable def postcompIso
    (hX : ProjectionChoice u X)
    (G : Y ⟶ Z) :
    Bicategory.postcomp (FiberedCategoryOver.pushforward u X hX) G ⋙
        homFunctor u hX Z ≅
      homFunctor u hX Y ⋙
        Bicategory.postcomp X (Pullback.mapCanonical u G) :=
  NatIso.ofComponents
    (fun H ↦ Hom.postcompIso u H G)
    (fun τ ↦ Hom.map.postcomp u τ G)

/-- The forward component of target-variable Hom naturality is the explicit target comparison. -/
@[simp, stacks 04WI "Hom functor target naturality forward component"]
theorem postcompIso.hom.app
    {hX : ProjectionChoice u X}
    (G : Y ⟶ Z) (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) :
    (postcompIso u hX G).hom.app H =
      (Hom.postcompIso u H G).hom := sorry

/-- The inverse component of target-variable Hom naturality is the explicit inverse target
comparison. -/
@[simp, stacks 04WI "Hom functor target naturality inverse component"]
theorem postcompIso.inv.app
    {hX : ProjectionChoice u X}
    (G : Y ⟶ Z) (H : FiberedCategoryOver.pushforward u X hX ⟶ Y) :
    (postcompIso u hX G).inv.app H =
      (Hom.postcompIso u H G).inv := sorry

end homFunctor

/- Axiom audit: the non-Prop arrows of `postcompApp` are the two identity components supplied to
`CategoricalPullback.mkIso`. The reported `sorryAx` is confined to compatibility, naturality,
verticality, inverse-law proofs, and proof fields inherited from the source and target owners; the
construction does not use `obj.postcomp`, `eqToHom`, or `eqToIso` to choose either arrow. -/

end FiberedCategoryOver.Pushforward

end CategoryTheory
