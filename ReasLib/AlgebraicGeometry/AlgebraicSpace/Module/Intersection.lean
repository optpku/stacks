/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-!
# Intersection of a module with a pushforward

The object `F ∩ f_* G` associated to a module map `φ : G ⟶ f^* F` is the chosen
pullback of the adjunction unit `F ⟶ f_* f^* F` along `f_* φ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The pullback `F ∩ f_* G` of the adjunction unit `F ⟶ f_* f^* F` along `f_* φ`. -/
noncomputable abbrev intersectPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : G ⟶ (pullback f).obj F) : X.Modules :=
  Limits.pullback ((pullbackPushforwardAdjunction f).unit.app F) ((pushforward f).map φ)

/-- The projection `F ∩ f_* G ⟶ F`. -/
noncomputable abbrev intersectPushforward_fst {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : G ⟶ (pullback f).obj F) : intersectPushforward f φ ⟶ F :=
  Limits.pullback.fst ((pullbackPushforwardAdjunction f).unit.app F) ((pushforward f).map φ)

/-- The projection `F ∩ f_* G ⟶ f_* G`. -/
noncomputable abbrev intersectPushforward_snd {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : G ⟶ (pullback f).obj F) :
    intersectPushforward f φ ⟶ (pushforward f).obj G :=
  Limits.pullback.snd ((pullbackPushforwardAdjunction f).unit.app F) ((pushforward f).map φ)

/-- The two legs of `F ∩ f_* G` commute with the adjunction unit and `f_* φ`. -/
theorem intersectPushforward_condition {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : G ⟶ (pullback f).obj F) :
    intersectPushforward_fst f φ ≫ (pullbackPushforwardAdjunction f).unit.app F =
      intersectPushforward_snd f φ ≫ (pushforward f).map φ :=
  sorry

/-- The defining square of `F ∩ f_* G` is a pullback square in `X.Modules`. -/
theorem intersectPushforward_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : G ⟶ (pullback f).obj F) :
    IsPullback (intersectPushforward_fst f φ) (intersectPushforward_snd f φ)
      ((pullbackPushforwardAdjunction f).unit.app F) ((pushforward f).map φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
