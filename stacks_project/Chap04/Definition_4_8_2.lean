/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
The source needs a predicate on morphisms of presheaves whose pullbacks along all Yoneda sections
are representable. The generic candidate `Functor.relativelyRepresentable`, specialized to
`yoneda`, has exactly this meaning: its witnesses exhibit the fibre products as Yoneda objects.
`MorphismProperty.relative` adds an unrelated morphism property, while `Functor.IsRepresentable`
classifies only one presheaf. Tagging the Yoneda specialization therefore avoids a parallel bridge
and exposes the canonical represented-pullback API for downstream use.
-/

/- Definition 4.8.2: a morphism `a : F ⟶ G` of presheaves is representable, or equivalently
`F` is relatively representable over `G`, when for every `U : C` and section
`ξ : yoneda.obj U ⟶ G`, the fibre product `yoneda.obj U ×[G] F` is representable. This is the
canonical morphism property `yoneda.relativelyRepresentable`. -/
@[stacks 0023 "relative representability of a presheaf morphism via Yoneda pullbacks"]
#check (yoneda.relativelyRepresentable : MorphismProperty (Cᵒᵖ ⥤ Type v))

end CategoryTheory
