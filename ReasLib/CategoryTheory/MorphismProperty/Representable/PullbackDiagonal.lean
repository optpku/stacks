/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-! Actual represented pullbacks for the diagonal of a presheaf fiber product.
The representing scheme and its universal lift are specified. Only equations
and universal-property laws of those specified maps remain proof obligations. -/

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
    dsimp [xH, yH, xF, yF, xG, yG] at *
    sorry)
  let W := Limits.pullback a b
  let fst : yoneda.obj W ⟶ yoneda.obj A :=
    yoneda.map (Limits.pullback.fst a b) ≫ rF.fst yF
  let snd : W ⟶ B := Limits.pullback.fst a b ≫ rF.snd yF
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
      (by sorry)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fst := fst) (snd := yoneda.map snd) (by sorry) lift
    (by sorry) (by sorry) (by sorry))

/-- The fiber product has a represented diagonal with actual representing objects and maps. -/
theorem diagonal : yoneda.relativelyRepresentable (Limits.diag (Limits.pullback f g)) :=
  Functor.relativelyRepresentable.diag_of_map_from_obj
    (fun {_} x ↦ sectionRepresentable f g hF hG hH x)

end CategoryTheory.Functor.relativelyRepresentable.PullbackDiagonal
