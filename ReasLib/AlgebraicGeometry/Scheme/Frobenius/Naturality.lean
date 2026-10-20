/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative

/-!
# Naturality of relative Frobenius

This leaf supplies the functorial map between Frobenius twists and the
commuting square relating it to relative Frobenius.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

section

variable {p : ℕ} [Fact p.Prime]
variable {X Y S : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (f : X ⟶ Y)
variable [Scheme.IsCharP S p]

/-- The map `X^(p/S) ⟶ Y^(p/S)` induced by a morphism `f : X ⟶ Y` over `S`. -/
@[stacks 0CCA]
def relativeFrobeniusTargetMap (h_over : f ≫ y = x) :
    pullback x (Scheme.absoluteFrobenius p S) ⟶ pullback y (Scheme.absoluteFrobenius p S) :=
  pullback.map x (Scheme.absoluteFrobenius p S) y (Scheme.absoluteFrobenius p S) f (𝟙 S) (𝟙 S)
    (by simpa using h_over.symm) (by simp)

/-- Relative Frobenius is natural for morphisms of schemes over a characteristic-`p` base. -/
@[stacks 0CCA]
theorem relativeFrobenius_commSq (h_over : f ≫ y = x) :
    CommSq
      (relativeFrobenius (p := p) x)
      f
      (relativeFrobeniusTargetMap (p := p) x y f h_over)
      (relativeFrobenius (p := p) y) := sorry

end

end AlgebraicGeometry.Scheme.Hom
