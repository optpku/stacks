/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.DualNumberPullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger

/-!
# Sections over dual-number pullbacks

For a cofibered category satisfying Schlessinger's second condition, a
commutative square over the dual-number pullback admits a section exactly when
the lower morphism lifts through the dual-number leg.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A square over the dual-number pullback has a section precisely when its lower leg lifts. -/
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

end CategoryTheory.Functor
