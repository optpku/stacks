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
    LocallyOfFiniteType (⊤_ (SchemeOverField k)).hom := by
  let e : (⊤_ (SchemeOverField k)) ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal
  have h : e.hom.left = (⊤_ (SchemeOverField k)).hom := by
    simpa only [Category.comp_id] using! e.hom.w
  haveI : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  rw [← h]
  exact MorphismProperty.of_isIso (P := @LocallyOfFiniteType) e.hom.left


/-- The product projections over a field form a pullback square against the maps to the
terminal scheme over that field. -/
theorem productIsPullback (X : SchemeOverField k) {Y : SchemeOverField k}
    (g : Y ⟶ ⊤_ (SchemeOverField k)) :
    IsPullback ((Limits.prod.fst : X ⨯ Y ⟶ X).left)
      ((Limits.prod.snd : X ⨯ Y ⟶ Y).left) (terminal.from X).left g.left := by
  have hg : terminal.from Y = g := Subsingleton.elim _ _
  simpa only [Over.forget_obj, Over.forget_map, hg] using
    (IsPullback.of_hasBinaryProduct' X Y).map (Over.forget _)

/-- The canonical pullback comparison with `X ⨯ Y` respects the structure maps. -/
theorem productIsoOfIsPullback_hom_base
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (square.isoIsPullback X.left Y.left (productIsPullback X g)).hom ≫
        (X ⨯ Y).hom = X'.hom := by
  rw [← (Limits.prod.fst : X ⨯ Y ⟶ X).w, ← Category.assoc,
    square.isoIsPullback_hom_fst]
  exact i.w

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
      (Limits.prod.snd : X ⨯ Y ⟶ Y).left (productIsPullback X g).w) (by
        rw [← i.w, ← Category.assoc, square.lift_fst]
        exact (Limits.prod.fst : X ⨯ Y ⟶ X).w)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply square.hom_ext
    · simpa only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc,
        IsPullback.lift_fst, Category.id_comp] using
        congrArg (fun h : X' ⟶ X ↦ h.left) (Limits.prod.lift_fst i f')
    · simpa only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc,
        IsPullback.lift_snd, Category.id_comp] using
        congrArg (fun h : X' ⟶ Y ↦ h.left) (Limits.prod.lift_snd i f')
  inv_hom_id := by
    apply Limits.prod.hom_ext
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, Limits.prod.lift_fst, Category.id_comp, Over.comp_left,
        Over.homMk_left, IsPullback.lift_fst]
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, Limits.prod.lift_snd, Category.id_comp, Over.comp_left,
        Over.homMk_left, IsPullback.lift_snd]

/-- The product comparison followed by the first projection is the given map to `X`. -/
theorem productIsoOfIsPullback_hom_fst
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.fst = i :=
  Limits.prod.lift_fst i f'

/-- The product comparison followed by the second projection is the given map to `Y`. -/
theorem productIsoOfIsPullback_hom_snd
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.snd = f' :=
  Limits.prod.lift_snd i f'

/-- The explicit product lift agrees with the comparison supplied by the two
pullback squares. This identifies both choices by their projections. -/
theorem productIsoOfIsPullback_hom_left
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom.left =
      (square.isoIsPullback X.left Y.left (productIsPullback X g)).hom := by
  apply (productIsPullback X g).hom_ext
  · rw [← Over.comp_left, productIsoOfIsPullback_hom_fst,
      square.isoIsPullback_hom_fst]
  · rw [← Over.comp_left, productIsoOfIsPullback_hom_snd,
      square.isoIsPullback_hom_snd]

/-- The product comparison is also the over-scheme lift of the pullback comparison. -/
theorem productIsoOfIsPullback_eq_isoMk
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    productIsoOfIsPullback X i f' g square =
      Over.isoMk (square.isoIsPullback X.left Y.left (productIsPullback X g))
        (productIsoOfIsPullback_hom_base X i f' g square) := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  exact productIsoOfIsPullback_hom_left X i f' g square

end AlgebraicGeometry.SchemeOverField
