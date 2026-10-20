/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The structure morphism of the terminal scheme over a field is locally of finite type. -/
instance instTerminalLocallyOfFiniteType :
    LocallyOfFiniteType (⊤_ (SchemeOverField k)).hom := sorry

/-- The product projections over a field form a pullback square against the maps to the
terminal scheme over that field. -/
theorem productIsPullback (X : SchemeOverField k) {Y : SchemeOverField k}
    (g : Y ⟶ ⊤_ (SchemeOverField k)) :
    IsPullback ((Limits.prod.fst : X ⨯ Y ⟶ X).left)
      ((Limits.prod.snd : X ⨯ Y ⟶ Y).left) (terminal.from X).left g.left := sorry

/-- The canonical isomorphism from a cartesian representative over a field to its product
representative has maps determined by the product and pullback universal properties. -/
noncomputable def productIsoOfIsPullback
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    X' ≅ X ⨯ Y where
  hom := Limits.prod.lift i f'
  inv := Over.homMk
    (square.lift (Limits.prod.fst : X ⨯ Y ⟶ X).left
      (Limits.prod.snd : X ⨯ Y ⟶ Y).left (productIsPullback X g).w) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The product comparison followed by the first projection is the given map to `X`. -/
theorem productIsoOfIsPullback_hom_fst
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.fst = i := sorry

/-- The product comparison followed by the second projection is the given map to `Y`. -/
theorem productIsoOfIsPullback_hom_snd
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.snd = f' := sorry

end AlgebraicGeometry.SchemeOverField
