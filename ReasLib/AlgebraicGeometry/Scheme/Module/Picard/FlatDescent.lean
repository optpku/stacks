/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.GenericFiber
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Flat descent of invertible modules

This file records descent of an invertible module that is trivial on the
generic fiber of a flat morphism with integral fibers.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FlatDescent

/-- An invertible module on the source of a flat morphism descends from the
target when the target is integral and normal, all fibers are integral, and
the module is trivial on the generic fiber. -/
@[stacks 0BD7]
theorem existsInvertiblePullback
    {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsIntegral Y]
    (hYnormal : Y.isNormal) [Flat φ]
    (hfibers : ∀ y : Y, IsIntegral (Scheme.Hom.fiber φ y))
    (hqc_or_lft : QuasiCompact φ ∨ LocallyOfFiniteType φ)
    (L : X.Modules) [Scheme.Modules.Invertible L]
    (hgeneric :
      Nonempty (((Scheme.Modules.pullback (Scheme.Hom.fiberι φ (genericPoint Y))).obj L) ≅
        (SheafOfModules.unit (Scheme.Hom.fiber φ (genericPoint Y)).ringCatSheaf :
          (Scheme.Hom.fiber φ (genericPoint Y)).Modules))) :
    ∃ (N : Y.Modules) (_ : Scheme.Modules.Invertible N),
      Nonempty (L ≅ (Scheme.Modules.pullback φ).obj N) := sorry

end AlgebraicGeometry.Scheme.Hom.FlatDescent
