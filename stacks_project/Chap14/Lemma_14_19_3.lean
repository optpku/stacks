/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Degreewise
import StacksCheckRecall

/-!
@stack 0184

# Lemma 14.19.3 compatibility facade

The reusable content is `SimplicialObject.Truncated.coskeleton.degree.inRange.iso`, the
truncated-simplex specialization of the generic fully faithful right-Kan-extension owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {m n : ℕ} (hn : n ≤ m)
variable (U : SimplicialObject.Truncated C m)

/- Lemma 14.19.3: in a degree already present in the truncation, the matching limit is canonically
isomorphic to the original degree-`n` object. -/
@[stacks 0184]
#check
  (SimplicialObject.Truncated.coskeleton.degree.inRange.iso U hn :
    limit (SimplicialObject.Truncated.coskeleton.degree.inRange.diagram U hn) ≅
      U.obj (op ⦋n, hn⦌ₘ))

variable [U.HasPointwiseCoskeleton]

/- The reusable compatibility bridge identifies this limit coordinate with the component of the
objectwise right-Kan-extension counit. -/
@[stacks 0184 "Lemma 14.19.3: compatibility with the right Kan extension counit"]
#check
  (SimplicialObject.Truncated.coskeleton.degree.inRange.iso.counit U hn :
    (SimplicialObject.Truncated.coskeleton.degree.isoLimit U ⦋n⦌).hom ≫
        (SimplicialObject.Truncated.coskeleton.degree.inRange.iso U hn).hom =
      ((SimplexCategory.Truncated.inclusion m).op.rightKanExtensionCounit U).app
        (op ⦋n, hn⦌ₘ))

end CategoryTheory
