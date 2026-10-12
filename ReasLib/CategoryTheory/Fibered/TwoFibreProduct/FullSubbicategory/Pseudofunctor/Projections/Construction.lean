/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Projections.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection transformations for full-subbicategory two-fibre products

The canonical endpoint projections assembled as strong transformations.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

variable (P) in
/-- The canonical first projection from the full-subbicategory two-fibre-product
pseudofunctor to the left-endpoint projection on bundled cospans. -/
@[stacks 0040 "first projection strong transformation for full-subbicategory two-fibre-products"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor P)
      (Bicategory.Cospan.leftProjection P.FullSubbicategory) where
  app S := _root_.CategoryTheory.TwoFibreProduct.fst S.fst S.snd
  naturality := pseudofunctor.fstIso
  naturality_naturality := pseudofunctor.fstIso.naturality.map₂
  naturality_id := pseudofunctor.fstIso.id
  naturality_comp := pseudofunctor.fstIso.comp

variable (P) in
/-- The canonical second projection from the full-subbicategory two-fibre-product
pseudofunctor to the right-endpoint projection on bundled cospans. -/
@[stacks 0040 "second projection strong transformation for full-subbicategory two-fibre-products"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor P)
      (Bicategory.Cospan.rightProjection P.FullSubbicategory) where
  app S := _root_.CategoryTheory.TwoFibreProduct.snd S.fst S.snd
  naturality := pseudofunctor.sndIso
  naturality_naturality := pseudofunctor.sndIso.naturality.map₂
  naturality_id := pseudofunctor.sndIso.id
  naturality_comp := pseudofunctor.sndIso.comp

/- Data and axiom audit (mathlib 4.32):

`pseudofunctor.fst` and `pseudofunctor.snd` reuse the explicit selected projections and
comparison isomorphisms. Their non-`Prop` fields contain no new choice or placeholder data;
`sorryAx` is confined to Prop-valued strong-transformation coherence fields. -/

end TwoFibreProduct

end CategoryTheory
