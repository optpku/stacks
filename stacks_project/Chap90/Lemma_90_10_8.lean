/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Lifting

/-!
# Lifting along a small extension after pushforward

The source-facing entry for Lemma 90.10.8 checks the canonical shared lifting
statement for a small-extension cospan and its explicit kernel-difference map.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

/- Lemma 90.10.8 -/
@[stacks 06IT] #check (CategoryTheory.Functor.exists_hom_of_pushforward :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k),
      [CategoryTheory.Functor.IsPredeformationCategory p] →
      [CategoryTheory.Functor.HasSchlessingerS2 p] →
      ∀ {A A1 A2 : ArtinianLocalAlgCat Λ k},
      (f1 : A1 ⟶ A) → (f2 : A2 ⟶ A) → [IsSmallExtension f2] →
      (h : A1 ⟶ A2) → (hh : h ≫ f2 = f1) →
      ∀ {y x1 x2 x : F},
      (c : y ⟶ x2) → (d : y ⟶ x1) → (a2 : x2 ⟶ x) → (a1 : x1 ⟶ x) →
      CommSq c d a2 a1 →
      p.IsHomLift (cospanPullbackSnd f1 f2 h hh) c →
      p.IsHomLift (cospanPullbackFst f1 f2 h hh) d →
      p.IsHomLift f2 a2 → p.IsHomLift f1 a1 →
      ∀ {gy : F},
      (φ : y ⟶ gy) →
      p.IsHomLift (cospanPullbackDiff h hh) φ →
      Nonempty (x1 ⟶ gy) → ∃ b : x1 ⟶ x2, b ≫ a2 = a1)
