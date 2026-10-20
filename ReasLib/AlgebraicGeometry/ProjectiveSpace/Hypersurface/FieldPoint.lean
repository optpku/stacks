/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- A morphism `X ⟶ P^1_k` matches `(x0 : x1 : x2 : x3) ↦ (x0 : x1)` on
field-valued points of the hypersurface whenever `x0` or `x1` is nonzero. -/
def IsCoordinateProjectionOnFieldPoints {k : Type u} [Field k] {d : ℕ}
    (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 d)
    (f : scheme 3 d F hF ⟶ ProjectiveSpace.scheme k 1) : Prop :=
  ∀ {L : Type u} [Field L] (φ : k →+* L)
    (v : Fin 4 → L) (hv : v ≠ 0) (w : Fin 2 → L) (hw : w ≠ 0),
    MvPolynomial.eval₂ φ v F = 0 → w 0 = v 0 → w 1 = v 1 →
      ∀ g : Spec (CommRingCat.of L) ⟶ scheme 3 d F hF,
        g ≫ closedImmersion 3 d F hF = ProjectiveSpace.homOf φ hv →
          g ≫ f = ProjectiveSpace.homOf φ hw

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
