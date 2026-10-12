/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Subterminal
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
public import ReasLib.CategoryTheory.Sites.Topos.Embedding

/-!
# Embeddings from category-of-elements localizations

This leaf records the Prop-level embedding criterion for the canonical topos
morphism presented by the category of elements of a sheaf.  The localization
site and the induced morphism themselves remain owned by `CategoryOfElements`.
-/

@[expose] public section

universe u v

namespace CategoryTheory

namespace Sheaf

namespace Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The category-of-elements localization at a sheaf is an embedding exactly
when the sheaf is subterminal. -/
@[stacks 08LW]
theorem isSubterminal_iff_isEmbedding
    (F : Sheaf J (Type v))
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
      (localizationProjection F).op.HasPointwiseRightKanExtension G] :
    IsSubterminal F ↔ (localizationMorphismOfTopoiIn F).IsEmbedding := sorry

/-- Lemma 7.43.3: a sheaf is a subobject of the terminal sheaf exactly when
its category-of-elements localization is an embedding of topoi. -/
@[stacks 08LW]
theorem mono_terminal_from_iff_isEmbedding
    (F : Sheaf J (Type v))
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
      (localizationProjection F).op.HasPointwiseRightKanExtension G] :
    Mono (Limits.terminal.from F) ↔ (localizationMorphismOfTopoiIn F).IsEmbedding := sorry

end Localization

end Sheaf

end CategoryTheory
