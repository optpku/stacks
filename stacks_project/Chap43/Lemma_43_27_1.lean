/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.VarietyCodimension.Pullback

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.VarietyCodimension

/- Lemma 43.27.1 (1): graph pullback on codimension-graded ordinary Chow groups
is a ring map. -/
@[stacks 0B2X] #check
  (AlgebraicGeometry.ChowGroup.VarietyCodimension.pullback_isGradedRingMap :
    ∀ {k : Type u} [Field k]
      {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
      (f : X ⟶ Y), IsGradedRingMap f)

/- Lemma 43.27.1 (2): graph pullback on ordinary Chow groups is
contravariantly functorial. -/
@[stacks 0B2X] #check
  (AlgebraicGeometry.ChowGroup.VarietyCodimension.pullback_comp :
    ∀ {k : Type u} [Field k]
      {X Y Z : SchemeOverField k}
      [ProjectiveVariety X] [ProjectiveVariety Y] [ProjectiveVariety Z]
      [Scheme.Regular X.left] [Scheme.Regular Y.left] [Scheme.Regular Z.left]
      [IsAlgClosed k] (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ)
      (alpha : Class Z p),
      pullback (f ≫ g) p alpha = pullback f p (pullback g p alpha))

/- Lemma 43.27.1 (3): graph pullback and proper pushforward on ordinary Chow
classes satisfy the projection formula. -/
@[stacks 0B2X] #check
  (AlgebraicGeometry.ChowGroup.VarietyCodimension.pullback_projectionFormula :
    ∀ {k : Type u} [Field k]
      {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
      (f : X ⟶ Y) (n q : ℤ)
      (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X n) (beta : Class Y q)
      (leftProduct : RelativeChow (fun _ ↦ (0 : ℤ)) Y (n - q))
      (rightProduct : RelativeChow (fun _ ↦ (0 : ℤ)) X (n - q))
      (_ : IsIntersectionProduct Y n ((Y.dimension : ℤ) - q) (n - q)
        (ChowGroup.map (fun _ ↦ (0 : ℤ)) X Y f n alpha) beta leftProduct)
      (_ : IsIntersectionProduct X n ((X.dimension : ℤ) - q) (n - q)
        alpha (pullback f q beta) rightProduct),
      leftProduct = ChowGroup.map (fun _ ↦ (0 : ℤ)) X Y f (n - q) rightProduct)

/- Lemma 43.27.1 (4): for a flat morphism, graph pullback on ordinary Chow
classes agrees with the previously defined flat pullback. -/
@[stacks 0B2X] #check
  (AlgebraicGeometry.ChowGroup.VarietyCodimension.pullback_eq_flatPullback :
    ∀ {k : Type u} [Field k]
      {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (p : ℤ) (alpha : Class Y p),
      HEq (pullback f p alpha)
        (ChowGroup.flatPullback (fun _ ↦ (0 : ℤ)) X Y f r
          ((Y.dimension : ℤ) - p) alpha))

end AlgebraicGeometry.ChowGroup.VarietyCodimension
