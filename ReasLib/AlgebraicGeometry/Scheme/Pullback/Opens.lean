/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Open restrictions of scheme pullbacks
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {S X Y : Scheme.{u}}

/-- The inclusion of an open subscheme of a pullback equalizes the two composites to the base. -/
@[stacks 02LJ]
theorem open_condition {U : Scheme.{u}} (f : X ⟶ S) (φ : U ⟶ S)
    (V : (pullback f φ : Scheme).Opens) :
    V.ι ≫ pullback.fst f φ ≫ f = V.ι ≫ pullback.snd f φ ≫ φ := sorry

/-- The morphism from a pullback of compatible open restrictions to the original
pullback. -/
@[stacks 01JR]
noncomputable def mapResLE
    (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    pullback (f.resLE U V hV) (g.resLE U W hW) ⟶ pullback f g :=
  pullback.map (f.resLE U V hV) (g.resLE U W hW) f g V.ι W.ι U.ι
    (Scheme.Hom.resLE_comp_ι f hV) (Scheme.Hom.resLE_comp_ι g hW)

/-- The restriction map to the original pullback followed by the first projection is the first
restricted projection followed by the open immersion. -/
@[reassoc (attr := simp), stacks 01JR "restricted pullback map first projection"]
theorem mapResLE_fst
    (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    mapResLE f g U V W hV hW ≫ pullback.fst f g =
      pullback.fst (f.resLE U V hV) (g.resLE U W hW) ≫ V.ι := sorry

/-- The restriction map to the original pullback followed by the second projection is the second
restricted projection followed by the open immersion. -/
@[reassoc (attr := simp), stacks 01JR "restricted pullback map second projection"]
theorem mapResLE_snd
    (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    mapResLE f g U V W hV hW ≫ pullback.snd f g =
      pullback.snd (f.resLE U V hV) (g.resLE U W hW) ≫ W.ι := sorry

/-- Restricting both factors and the base open induces an open immersion into the
original pullback. -/
@[stacks 01JR]
theorem mapResLE_isOpenImmersion
    (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    IsOpenImmersion (mapResLE f g U V W hV hW) := sorry

/-- The image of the restricted pullback is the intersection of the inverse images
of the two chosen opens. -/
@[stacks 01JR]
theorem opensRange_mapResLE
    (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    Scheme.Hom.opensRange (H := mapResLE_isOpenImmersion f g U V W hV hW)
        (mapResLE f g U V W hV hW) =
      (pullback.fst f g) ⁻¹ᵁ V ⊓ (pullback.snd f g) ⁻¹ᵁ W := sorry

/-- Restricting a commutative square to four compatible opens gives a commutative square. -/
theorem restrictedCommSq
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a)
    (V' : Y'.Opens) (V : Y.Opens) (U' : X'.Opens) (U : X.Opens)
    (hb : V' ≤ b ⁻¹ᵁ V) (hf' : V' ≤ f' ⁻¹ᵁ U')
    (hf : V ≤ f ⁻¹ᵁ U) (ha : U' ≤ a ⁻¹ᵁ U) :
    CommSq (b.resLE V V' hb) (f'.resLE U' V' hf')
      (f.resLE U V hf) (a.resLE U U' ha) := sorry

/-- The canonical pullback lift for a restriction of an open-pullback square is an open
immersion. -/
theorem restrictedLiftIsOpenImmersion
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    (V' : Y'.Opens) (V : Y.Opens) (U' : X'.Opens) (U : X.Opens)
    (hb : V' ≤ b ⁻¹ᵁ V) (hf' : V' ≤ f' ⁻¹ᵁ U')
    (hf : V ≤ f ⁻¹ᵁ U) (ha : U' ≤ a ⁻¹ᵁ U) :
    IsOpenImmersion
      (pullback.lift (b.resLE V V' hb) (f'.resLE U' V' hf')
        (restrictedCommSq b f' f a sq V' V U' U hb hf' hf ha).w) := sorry

end AlgebraicGeometry.Scheme.Pullback
