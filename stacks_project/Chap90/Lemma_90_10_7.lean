module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Lemma_90_10_7_DualNumber
public import stacks_project.Chap90.Lemma_90_10_7_Pullback

/-!
# Lifting sections over the dual-number pullback

If a category cofibered in groupoids over `C_Λ` satisfies (S2), a morphism `a`
in a square lying over `A ×_k DualNumber k → DualNumber k` over `A → k` has a
section if and only if `d` lifts through `e`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.10.7: let `p : F ⥤ ArtinianLocalAlgCat Λ k` be cofibered in groupoids and
satisfy (S2). For a commutative square `CommSq c a e d` in `F` lying over the
dual-number pullback square
`dualNumberPullback A ⟶ dualNumber Λ k` over `A ⟶ residue Λ k`, there exists
`s : x ⟶ y` with `s ≫ a = 𝟙 x` if and only if there exists `sε : x ⟶ xε` with
`sε ≫ e = d`. -/
@[stacks 06IS]
theorem exists_section_iff_exists_lift (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (A : ArtinianLocalAlgCat Λ k) {y x xε x0 : F}
    (c : y ⟶ xε) (a : y ⟶ x) (e : xε ⟶ x0) (d : x ⟶ x0)
    (h_sq : CommSq c a e d)
    (hc : p.IsHomLift (dualNumberPullbackSnd A) c)
    (ha : p.IsHomLift (dualNumberPullbackFst A) a)
    (he : p.IsHomLift (dualNumberToResidue Λ k) e)
    (hd : p.IsHomLift (toResidue A) d) :
    (∃ s : x ⟶ y, s ≫ a = 𝟙 x) ↔ (∃ sε : x ⟶ xε, sε ≫ e = d) := sorry

/-- A section of `a` yields a lift of `d` through `e`. -/
theorem exists_lift_of_section (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (A : ArtinianLocalAlgCat Λ k) {y x xε x0 : F}
    (c : y ⟶ xε) (a : y ⟶ x) (e : xε ⟶ x0) (d : x ⟶ x0)
    (h_sq : CommSq c a e d)
    (hc : p.IsHomLift (dualNumberPullbackSnd A) c)
    (ha : p.IsHomLift (dualNumberPullbackFst A) a)
    (he : p.IsHomLift (dualNumberToResidue Λ k) e)
    (hd : p.IsHomLift (toResidue A) d) :
    (∃ s : x ⟶ y, s ≫ a = 𝟙 x) → ∃ sε : x ⟶ xε, sε ≫ e = d := sorry

/-- A lift of `d` through `e` yields a section of `a`. -/
theorem exists_section_of_lift (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (A : ArtinianLocalAlgCat Λ k) {y x xε x0 : F}
    (c : y ⟶ xε) (a : y ⟶ x) (e : xε ⟶ x0) (d : x ⟶ x0)
    (h_sq : CommSq c a e d)
    (hc : p.IsHomLift (dualNumberPullbackSnd A) c)
    (ha : p.IsHomLift (dualNumberPullbackFst A) a)
    (he : p.IsHomLift (dualNumberToResidue Λ k) e)
    (hd : p.IsHomLift (toResidue A) d) :
    (∃ sε : x ⟶ xε, sε ≫ e = d) → ∃ s : x ⟶ y, s ≫ a = 𝟙 x := sorry

end CategoryTheory.Functor
