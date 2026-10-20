/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import ReasLib.CategoryTheory.ObjectProperty.Cover

/-!
# Opposite Epi Covers and Mono Embeddings

This leaf transports the two object-property replacement conditions through
Mathlib's canonical `ObjectProperty.op` and `ObjectProperty.unop` operations.
It also records their monotonicity under enlargement of an object property.
-/

@[expose] public section

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

namespace HasEpiCover

/-- Taking opposites turns epi covers into mono embeddings. -/
instance op (P : ObjectProperty C) [P.HasEpiCover] :
    P.op.HasMonoEmbedding := sorry

/-- Transporting an epi-cover property back from the opposite category gives mono embeddings. -/
instance unop (P : ObjectProperty Cᵒᵖ) [P.HasEpiCover] :
    P.unop.HasMonoEmbedding := sorry

/-- Mono embeddings of the opposite property give epi covers of the original property. -/
theorem of_op (P : ObjectProperty C) [P.op.HasMonoEmbedding] :
    P.HasEpiCover := sorry

/-- Mono embeddings of the unop property give epi covers in the opposite category. -/
theorem of_unop (P : ObjectProperty Cᵒᵖ) [P.unop.HasMonoEmbedding] :
    P.HasEpiCover := sorry

/-- Epi covers persist after enlarging the object property. -/
theorem of_le {P Q : ObjectProperty C} [P.HasEpiCover] (hPQ : P ≤ Q) :
    Q.HasEpiCover := sorry

end HasEpiCover

namespace HasMonoEmbedding

/-- Taking opposites turns mono embeddings into epi covers. -/
instance op (P : ObjectProperty C) [P.HasMonoEmbedding] :
    P.op.HasEpiCover := sorry

/-- Transporting a mono-embedding property back from the opposite category gives epi covers. -/
instance unop (P : ObjectProperty Cᵒᵖ) [P.HasMonoEmbedding] :
    P.unop.HasEpiCover := sorry

/-- Epi covers of the opposite property give mono embeddings of the original property. -/
theorem of_op (P : ObjectProperty C) [P.op.HasEpiCover] :
    P.HasMonoEmbedding := sorry

/-- Epi covers of the unop property give mono embeddings in the opposite category. -/
theorem of_unop (P : ObjectProperty Cᵒᵖ) [P.unop.HasEpiCover] :
    P.HasMonoEmbedding := sorry

/-- Mono embeddings persist after enlarging the object property. -/
theorem of_le {P Q : ObjectProperty C} [P.HasMonoEmbedding] (hPQ : P ≤ Q) :
    Q.HasMonoEmbedding := sorry

end HasMonoEmbedding

end CategoryTheory.ObjectProperty
