/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Projections.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection transformations for the explicit pseudo-pullback pseudofunctor

The canonical strong transformations to the left- and right-endpoint projections.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped Bicategory Pseudofunctor.StrongTrans

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable (C) in
/-- The canonical first projection from the explicit pseudo-pullback pseudofunctor to the
left-endpoint projection on bundled based cospans. -/
@[stacks 0040 "first projection strong transformation for explicit pseudo-pullbacks"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor C)
      (Bicategory.Cospan.leftProjection
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)) where
  app S := _root_.CategoryTheory.BasedCategory.PseudoPullback.fst S.fst S.snd
  naturality := pseudofunctor.fstIso
  naturality_naturality := pseudofunctor.fstIso.naturality.map₂
  naturality_id := pseudofunctor.fstIso.id
  naturality_comp := pseudofunctor.fstIso.comp

variable (C) in
/-- The canonical second projection from the explicit pseudo-pullback pseudofunctor to the
right-endpoint projection on bundled based cospans. -/
@[stacks 0040 "second projection strong transformation for explicit pseudo-pullbacks"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor C)
      (Bicategory.Cospan.rightProjection
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)) where
  app S := _root_.CategoryTheory.BasedCategory.PseudoPullback.snd S.fst S.snd
  naturality := pseudofunctor.sndIso
  naturality_naturality := pseudofunctor.sndIso.naturality.map₂
  naturality_id := pseudofunctor.sndIso.id
  naturality_comp := pseudofunctor.sndIso.comp

/- Data and axiom audit (mathlib 4.32):

`pseudofunctor.fst` and `pseudofunctor.snd` reuse the explicit projection maps and comparison
isomorphisms. Their non-Prop fields therefore contain no new choice or placeholder data.
`#print axioms` may report `sorryAx` only through the Prop-valued naturality, identity, and
composition coherence fields deferred in this statement-stage file. -/

end

end PseudoPullback

end BasedCategory

end CategoryTheory
