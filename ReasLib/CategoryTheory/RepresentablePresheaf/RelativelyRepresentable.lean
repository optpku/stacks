/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Data.List.TFAE
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative representability criteria for presheaves

Relative representability is stable over a representable codomain.  For a presheaf, relative
representability of the diagonal can be tested either on all sections or on pairwise pullbacks of
representable sections.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Functor.relativelyRepresentable

/-- Lemma 4.8.3 (Stacks 03KC): a relatively representable morphism with representable codomain
has representable domain. -/
@[stacks 03KC]
theorem domain_isRepresentable
    {F G : Cᵒᵖ ⥤ Type v} (a : F ⟶ G)
    (ha : yoneda.relativelyRepresentable a) (hG : G.IsRepresentable) :
    F.IsRepresentable := sorry

section Diagonal

/-- Relative representability of all representable sections is equivalent to representability of
all their pairwise pullbacks. -/
theorem sections_iff_pairwisePullbacks
    (F : Cᵒᵖ ⥤ Type v) :
    (∀ (U : C) (ξ : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable ξ) ↔
      ∀ (U V : C) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
        (Limits.pullback ξ ξ').IsRepresentable := sorry

variable [HasBinaryProducts C]

/-- Relative representability of the diagonal is equivalent to representability of every
pairwise pullback of representable sections. -/
theorem diag_iff_pairwisePullbacks
    (F : Cᵒᵖ ⥤ Type v) :
    yoneda.relativelyRepresentable (Limits.diag F) ↔
      ∀ (U V : C) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
        (Limits.pullback ξ ξ').IsRepresentable := sorry

/-- Lemma 4.8.4 (Stacks 0024): relative representability of the diagonal, relative
representability of every representable section, and representability of all pairwise section
pullbacks are equivalent. -/
@[stacks 0024]
theorem diag_tfae (F : Cᵒᵖ ⥤ Type v) :
    [yoneda.relativelyRepresentable (Limits.diag F),
      ∀ (U : C) (ξ : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable ξ,
      ∀ (U V : C) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
        (Limits.pullback ξ ξ').IsRepresentable].TFAE := sorry

end Diagonal

end Functor.relativelyRepresentable

end CategoryTheory
