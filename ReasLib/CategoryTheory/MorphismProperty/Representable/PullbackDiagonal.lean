/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-! Represented pullbacks for the diagonal of a presheaf fiber product are obtained
by taking fiber products of the represented pairwise pullbacks. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u

namespace CategoryTheory.Functor.relativelyRepresentable.PullbackDiagonal
variable {S : Scheme.{u}}
variable {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
variable (hF : yoneda.relativelyRepresentable (Limits.diag F))
variable (hG : yoneda.relativelyRepresentable (Limits.diag G))
variable (hH : yoneda.relativelyRepresentable (Limits.diag H))

include hF hG hH

/-- A represented section into the fiber product has represented pullbacks: take the
fiber product of its pairwise F- and G-pullbacks over the pairwise H-pullback. -/
theorem sectionRepresentable {A : Over S} (x : yoneda.obj A ⟶ Limits.pullback f g) :
    yoneda.relativelyRepresentable x := by
  intro B y
  let xF := x ≫ Limits.pullback.fst f g
  let yF := y ≫ Limits.pullback.fst f g
  let xG := x ≫ Limits.pullback.snd f g
  let yG := y ≫ Limits.pullback.snd f g
  let xH := xF ≫ f
  let yH := yF ≫ f
  let rF := Functor.relativelyRepresentable.of_diag hF xF
  let rG := Functor.relativelyRepresentable.of_diag hG xG
  let rH := Functor.relativelyRepresentable.of_diag hH xH
  let WF := rF.pullback yF
  let WG := rG.pullback yG
  let WH := rH.pullback yH
  let a : WF ⟶ WH := rH.lift (g := yH) (rF.fst yF) (rF.snd yF) (by
    simpa only [xH, yH, Category.assoc] using congrArg (fun k ↦ k ≫ f) (rF.w yF))
  let b : WG ⟶ WH := rH.lift (g := yH) (rG.fst yG) (rG.snd yG) (by
    have hx : xF ≫ f = xG ≫ g := by
      simp only [xF, xG, Category.assoc, Limits.pullback.condition]
    have hy : yF ≫ f = yG ≫ g := by
      simp only [yF, yG, Category.assoc, Limits.pullback.condition]
    dsimp only [xH, yH]
    rw [hx, hy, ← Category.assoc, rG.w yG, Category.assoc])
  let W := Limits.pullback a b
  let fst : yoneda.obj W ⟶ yoneda.obj A :=
    yoneda.map (Limits.pullback.fst a b) ≫ rF.fst yF
  let snd : W ⟶ B := Limits.pullback.fst a b ≫ rF.snd yF
  have hfst : yoneda.map (Limits.pullback.fst a b) ≫ rF.fst yF =
      yoneda.map (Limits.pullback.snd a b) ≫ rG.fst yG := by
    have h := congrArg (fun k ↦ yoneda.map k ≫ rH.fst yH)
      (Limits.pullback.condition (f := a) (g := b))
    simpa [Functor.map_comp, a, b, Category.assoc] using h
  have hsnd : Limits.pullback.fst a b ≫ rF.snd yF =
      Limits.pullback.snd a b ≫ rG.snd yG := by
    have h := congrArg (fun k ↦ k ≫ rH.snd yH)
      (Limits.pullback.condition (f := a) (g := b))
    simpa [a, b, Category.assoc] using h
  refine ⟨W, snd, fst, ?_⟩
  let lift : ∀ c : PullbackCone x y, c.pt ⟶ yoneda.obj W := fun c ↦
    (yoneda.map_isPullback (IsPullback.of_hasPullback a b)).lift
      ((rF.isPullback yF).lift c.fst c.snd (by
        dsimp [xF, yF]
        simpa only [Category.assoc] using
          congrArg (fun k ↦ k ≫ Limits.pullback.fst f g) c.condition))
      ((rG.isPullback yG).lift c.fst c.snd (by
        dsimp [xG, yG]
        simpa only [Category.assoc] using
          congrArg (fun k ↦ k ≫ Limits.pullback.snd f g) c.condition))
      (by
        apply (rH.isPullback yH).hom_ext
        · simp [a, b, Category.assoc]
        · simp only [a, b, Category.assoc]
          rw [← yoneda.map_comp, ← yoneda.map_comp]
          simp)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fst := fst) (snd := yoneda.map snd) (by
      apply Limits.pullback.hom_ext
      · simpa [fst, snd, Functor.map_comp, Category.assoc, xF, yF] using
          congrArg (fun k ↦ yoneda.map (Limits.pullback.fst a b) ≫ k) (rF.w yF)
      · change fst ≫ xG = yoneda.map snd ≫ yG
        calc
          fst ≫ xG = (yoneda.map (Limits.pullback.snd a b) ≫ rG.fst yG) ≫ xG :=
            congrArg (fun k ↦ k ≫ xG) hfst
          _ = yoneda.map (Limits.pullback.snd a b ≫ rG.snd yG) ≫ yG := by
            rw [Category.assoc, rG.w yG, ← Category.assoc, ← Functor.map_comp]
          _ = yoneda.map snd ≫ yG := by rw [← hsnd]) lift
    (by intro c; simp [lift, fst])
    (by intro c; simp [lift, snd, Functor.map_comp])
    (by
      intro c m hm₁ hm₂
      apply (yoneda.map_isPullback (IsPullback.of_hasPullback a b)).hom_ext
      · apply (rF.isPullback yF).hom_ext
        · simpa [lift, fst, Category.assoc] using hm₁
        · simpa [lift, snd, Functor.map_comp, Category.assoc] using hm₂
      · apply (rG.isPullback yG).hom_ext
        · simpa [lift, fst, Category.assoc, hfst] using hm₁
        · simpa [lift, snd, Functor.map_comp, Category.assoc, hsnd] using hm₂))

/-- The fiber product has a represented diagonal with actual representing objects and maps. -/
theorem diagonal : yoneda.relativelyRepresentable (Limits.diag (Limits.pullback f g)) :=
  Functor.relativelyRepresentable.diag_of_map_from_obj
    (fun {_} x ↦ sectionRepresentable f g hF hG hH x)

end CategoryTheory.Functor.relativelyRepresentable.PullbackDiagonal
