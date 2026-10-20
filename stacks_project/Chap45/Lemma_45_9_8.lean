/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.ProjectiveLine
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/- Lemma 45.9.8 (1): untwisted cohomology of a represented projective line has
dimension one in cohomological degree zero. -/
@[stacks 0FHI] #check
  (WeilCohomology.SchemeClassicalTheory.projectiveLineCohomologyFinrankZero :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      (X : V) (eX : T.scheme.obj X ≅ ProjectiveSpace.schemeOver k 1),
      Module.finrank F (Hgrade X (0, 0)) = 1)

/- Lemma 45.9.8 (2): untwisted cohomology of a represented projective line has
dimension one in cohomological degree two. -/
@[stacks 0FHI] #check
  (WeilCohomology.SchemeClassicalTheory.projectiveLineCohomologyFinrankTwo :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      (X : V) (eX : T.scheme.obj X ≅ ProjectiveSpace.schemeOver k 1),
      Module.finrank F (Hgrade X (2, 0)) = 1)

/- Lemma 45.9.8 (3): untwisted cohomology of a represented projective line
vanishes outside cohomological degrees zero and two. -/
@[stacks 0FHI] #check
  (WeilCohomology.SchemeClassicalTheory.projectiveLineCohomologyEqBot :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      (X : V) (eX : T.scheme.obj X ≅ ProjectiveSpace.schemeOver k 1)
      (i : ℤ) (hi0 : i ≠ 0) (hi2 : i ≠ 2),
      Hgrade X (i, 0) = ⊥)

/- Lemma 45.9.8 (4): the finrank of untwisted cohomology of a represented
projective line is one in degrees zero and two and zero otherwise. -/
@[stacks 0FHI] #check
  (WeilCohomology.SchemeClassicalTheory.projectiveLineCohomologyFinrank :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      (X : V) (eX : T.scheme.obj X ≅ ProjectiveSpace.schemeOver k 1) (i : ℤ),
      Module.finrank F (Hgrade X (i, 0)) = if i = 0 ∨ i = 2 then 1 else 0)

end WeilCohomology.SchemeClassicalTheory
