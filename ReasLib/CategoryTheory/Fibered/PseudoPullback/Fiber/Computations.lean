/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Equivalence

/-!
# Packaged-equivalence computations for fibres of based pseudo-pullbacks

This leaf exposes computations for the packaged fibre equivalence and its quasi-inverse.
Forward projection comparisons live in `Fiber.Projection.Forward`; inverse projection
comparisons that depend on the packaged equivalence live in `Fiber.Projection.Inverse`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS vX vY vS

namespace CategoryTheory
namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

noncomputable section

namespace PseudoPullback

namespace Fiber

/-- The inverse functor stored by the fibre quasi-inverse is the explicit comparison inverse. -/
@[simp]
theorem comparison.quasiInverse.inverse
    (U : C) :
    (comparison.quasiInverse F G U).inverse = comparisonInverse F G U := sorry

/-- The unit stored by the fibre quasi-inverse is the named outer-fibre comparison. -/
@[simp]
theorem comparison.quasiInverse.unitIso
    (U : C) :
    (comparison.quasiInverse F G U).unitIso = comparison.unitIso F G U := sorry

/-- The counit stored by the fibre quasi-inverse is the named categorical-pullback
comparison. -/
@[simp]
theorem comparison.quasiInverse.counitIso
    (U : C) :
    (comparison.quasiInverse F G U).counitIso = comparison.counitIso F G U := sorry

/-- The forward functor of the packaged fibre equivalence is the explicit functor to the
categorical-pullback model. -/
@[simp]
theorem comparison.equivalence.functor
    (U : C) :
    (comparison.equivalence F G U).functor = Fiber.comparison F G U := sorry

/-- The inverse functor of the packaged fibre equivalence is the canonical comparison from the
categorical-pullback model to the actual fibre. -/
@[simp]
theorem comparison.equivalence.inverse
    (U : C) :
    (comparison.equivalence F G U).inverse = comparisonInverse F G U := sorry

/-- Packaging the fibre quasi-inverse retains its explicit counit isomorphism. -/
@[simp]
theorem comparison.equivalence.counitIso
    (U : C) :
    (comparison.equivalence F G U).counitIso = comparison.counitIso F G U := sorry

/-- The packaged fibre unit is the canonical adjointification of the explicit unit against
the explicit counit. -/
theorem comparison.equivalence.unitIso
    (U : C) :
    (comparison.equivalence F G U).unitIso =
      Equivalence.adjointifyη
        (comparison.unitIso F G U) (comparison.counitIso F G U) := sorry

end Fiber

end PseudoPullback
end

end BasedCategory
end CategoryTheory
