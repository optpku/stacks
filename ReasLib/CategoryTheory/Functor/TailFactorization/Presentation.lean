/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Presentable.Finite
public import ReasLib.CategoryTheory.Functor.TailFactorization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tail factorization and colimit presentations

Tail factorization is independent of the chosen filtered presentation when all stages in both
presentations are finitely presentable.
-/

@[expose] public section

open CategoryTheory

universe u v w x

namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C] {X : C}
variable {I : Type w} [SmallCategory I] [IsFiltered I]
variable {J : Type x} [SmallCategory J] [IsFiltered J]

private theorem hasTailFactorization_of
    (P : ColimitPresentation I X) (Q : ColimitPresentation J X)
    (hPx : ∀ i, IsFinitelyPresentable.{x} (P.diag.obj i))
    (hQw : ∀ j, IsFinitelyPresentable.{w} (Q.diag.obj j))
    (hQx : ∀ j, IsFinitelyPresentable.{x} (Q.diag.obj j))
    (h : P.diag.HasTailFactorization) : Q.diag.HasTailFactorization := by
  intro j
  letI : IsFinitelyPresentable.{w} (Q.diag.obj j) := hQw j
  obtain ⟨i, a, ha⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit P.isColimit (Q.ι.app j)
  obtain ⟨i', f, hf⟩ := h i
  letI : IsFinitelyPresentable.{x} (P.diag.obj i') := hPx i'
  obtain ⟨j', b, hb⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit Q.isColimit (P.ι.app i')
  have haX : a ≫ (P.ι.app i : P.diag.obj i ⟶ X) =
      (Q.ι.app j : Q.diag.obj j ⟶ X) := ha
  have hbX : b ≫ (Q.ι.app j' : Q.diag.obj j' ⟶ X) =
      (P.ι.app i' : P.diag.obj i' ⟶ X) := hb
  have hwX : P.diag.map f ≫ (P.ι.app i' : P.diag.obj i' ⟶ X) =
      (P.ι.app i : P.diag.obj i ⟶ X) := P.w f
  let t : Q.diag.obj j ⟶ Q.diag.obj j' := a ≫ P.diag.map f ≫ b
  have ht : t ≫ Q.ι.app j' = Q.ι.app j := by
    change (a ≫ (P.diag.map f ≫ b)) ≫ (Q.ι.app j' : Q.diag.obj j' ⟶ X) =
      (Q.ι.app j : Q.diag.obj j ⟶ X)
    exact (Category.assoc a (P.diag.map f ≫ b) (Q.ι.app j')).trans
      ((congrArg (fun z ↦ a ≫ z) (Category.assoc (P.diag.map f) b (Q.ι.app j'))).trans
        ((congrArg (fun z ↦ a ≫ P.diag.map f ≫ z) hbX).trans
          ((congrArg (fun z ↦ a ≫ z) hwX).trans haX)))
  let l := IsFiltered.max j j'
  let p : j ⟶ l := IsFiltered.leftToMax j j'
  let q : j' ⟶ l := IsFiltered.rightToMax j j'
  have heq :
      Q.diag.map p ≫ Q.ι.app l = (t ≫ Q.diag.map q) ≫ Q.ι.app l := by
    rw [Q.w p, Category.assoc, Q.w q]
    exact ht.symm
  letI : IsFinitelyPresentable.{x} (Q.diag.obj j) := hQx j
  obtain ⟨m, r, s, hrs⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
    Q.isColimit (Q.diag.map p) (t ≫ Q.diag.map q) heq
  refine ⟨m, p ≫ r, fun k g ↦ ?_⟩
  letI : IsFinitelyPresentable.{w} (Q.diag.obj k) := hQw k
  obtain ⟨n, c, hc⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit P.isColimit (Q.ι.app k)
  have heq' : a ≫ P.ι.app i = (Q.diag.map g ≫ c) ≫ P.ι.app n := by
    rw [ha, Category.assoc, hc]
    exact (Q.w g).symm
  obtain ⟨o, d, e, hde⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
    P.isColimit a (Q.diag.map g ≫ c) heq'
  obtain ⟨z, hz⟩ := hf o d
  refine ⟨c ≫ P.diag.map e ≫ z ≫ b ≫ Q.diag.map (q ≫ s), ?_⟩
  calc
    Q.diag.map (p ≫ r) = Q.diag.map p ≫ Q.diag.map r := Q.diag.map_comp p r
    _ = (t ≫ Q.diag.map q) ≫ Q.diag.map s := hrs
    _ = a ≫ P.diag.map f ≫ b ≫ Q.diag.map q ≫ Q.diag.map s := by
      simp only [t, Category.assoc]
    _ = a ≫ P.diag.map d ≫ z ≫ b ≫ Q.diag.map q ≫ Q.diag.map s := by
      simp only [hz, Category.assoc]
    _ = Q.diag.map g ≫ c ≫ P.diag.map e ≫ z ≫ b ≫
        Q.diag.map q ≫ Q.diag.map s := by
      rw [reassoc_of% hde]
    _ = Q.diag.map g ≫
        (c ≫ P.diag.map e ≫ z ≫ b ≫ Q.diag.map (q ≫ s)) := by
      simp only [Q.diag.map_comp]

/-- Tail factorization is invariant under replacing a filtered colimit presentation by another
one whose stages are finitely presentable for both index universes.  The two universe instances
are separately necessary: one factors maps through the other presentation, while the other
detects equality inside the stage's own presentation. -/
@[stacks 059W "presentation invariance"]
theorem hasTailFactorization_iff
    (P : ColimitPresentation I X) (Q : ColimitPresentation J X)
    (hPw : ∀ i, IsFinitelyPresentable.{w} (P.diag.obj i))
    (hPx : ∀ i, IsFinitelyPresentable.{x} (P.diag.obj i))
    (hQw : ∀ j, IsFinitelyPresentable.{w} (Q.diag.obj j))
    (hQx : ∀ j, IsFinitelyPresentable.{x} (Q.diag.obj j)) :
    P.diag.HasTailFactorization ↔ Q.diag.HasTailFactorization :=
  ⟨hasTailFactorization_of P Q hPx hQw hQx,
    hasTailFactorization_of Q P hQw hPx hPw⟩

end CategoryTheory.Limits.ColimitPresentation
