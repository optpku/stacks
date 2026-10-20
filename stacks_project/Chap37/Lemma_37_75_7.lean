/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.FiberLength
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

#check (AlgebraicGeometry.Scheme.Hom.fiberWeight_apply :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
    f.fiberWeight x =
      ((Module.length (X.presheaf.stalk x)
            ((X.presheaf.stalk x) ⧸
              (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat *
          Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℕ))

/- Lemma 37.75.7: a locally quasi-finite, locally finitely presented, flat morphism has
the positive weighting given by local closed-fibre length times finite inseparable degree. -/
@[stacks 0F3D] #check
  (AlgebraicGeometry.Scheme.Hom.fiberWeight_isPositiveWeighting :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f],
      f.IsWeighting f.fiberWeight ∧ ∀ x : X, 0 < f.fiberWeight x)

end AlgebraicGeometry.Scheme.Hom
