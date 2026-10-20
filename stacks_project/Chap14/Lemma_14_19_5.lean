/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily.Cone
import StacksCheckRecall

/-!
@stack 0186

# Lemma 14.19.5 compatibility facade

ReasLib owns both presentations of matching families: explicit compatible face coordinates and
cones over the structured-arrow diagram. Their natural equivalence transports representability
to the canonical limit-cone API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Truncated
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (U_succ : C)
variable (R : (SimplicialObject.Truncated.matching.FaceFamily.presheaf U).RepresentableBy U_succ)

/- Lemma 14.19.5 (0186): if the explicit compatible face-family functor in positive degree is
represented by `U_succ`, then the induced cone with point `U_succ` is a limit cone. -/
@[stacks 0186]
#check (SimplicialObject.Truncated.matching.FaceFamily.limitCone.isLimit R :
  IsLimit (SimplicialObject.Truncated.matching.FaceFamily.limitCone R))

/- The reusable comparison identifies full matching cones with explicit compatible face
families, naturally in the test object. -/
#check (SimplicialObject.Truncated.matching.FaceFamily.coneIso U)

end CategoryTheory
