/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Projection.Forward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse projection comparisons for fibres of based pseudo-pullbacks

This leaf derives projection comparisons for the inverse of the packaged fibre equivalence from
the forward projection comparisons using `Iso.inverseCompIso`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
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

/-- The inverse fibre equivalence preserves the first projection. This is derived from the
forward comparison and the equivalence counit. -/
@[stacks 02XI "inverse first projection comparison for the fibre equivalence"]
noncomputable def comparison.equivalence.inverseFstIso (U : C) :
    (comparison.equivalence F G U).inverse ⋙
        (PseudoPullback.fst F G).fiberFunctor U ≅
      π₁ (F.fiberFunctor U) (G.fiberFunctor U) :=
  Iso.inverseCompIso (comparison.fstIso F G U).symm

/-- The inverse fibre equivalence preserves the second projection. This is derived from the
forward comparison and the equivalence counit. -/
@[stacks 02XI "inverse second projection comparison for the fibre equivalence"]
noncomputable def comparison.equivalence.inverseSndIso (U : C) :
    (comparison.equivalence F G U).inverse ⋙
        (PseudoPullback.snd F G).fiberFunctor U ≅
      π₂ (F.fiberFunctor U) (G.fiberFunctor U) :=
  Iso.inverseCompIso (comparison.sndIso F G U).symm

end Fiber
end PseudoPullback
end

end BasedCategory
end CategoryTheory
