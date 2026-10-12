/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Category.Preord
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.Comparison

/-!
# Comparison isomorphisms for order-embedding reindexing

This module specializes the neutral reindexing comparison data to functors
induced by order embeddings.  It has no fiber smallness assumptions.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w₀ w₁ w₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing.OrderEmbedding

variable {C : Type u} [Category.{v} C]
variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {S : ιᵒᵖ ⥤ C}

/-- The canonical inverse-system identification for the identity order-embedding reindexing. -/
noncomputable def idIso (S : ιᵒᵖ ⥤ C) :
    S ≅ ((OrderEmbedding.id ι).toOrderHom.toFunctor).op ⋙ S :=
  Reindexing.idIso S

/-- The canonical comparison isomorphism for two successive order-embedding reindexings. -/
noncomputable def compIso
    {ι'' : Type w₂} [Preorder ι'']
    {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U) :
    S ≅ ((j.comp k).toOrderHom.toFunctor).op ⋙ U :=
  Reindexing.compIso j.toOrderHom.toFunctor k.toOrderHom.toFunctor e e'

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing.OrderEmbedding
