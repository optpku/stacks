/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Algebraic.Morphisms
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace

universe w u

section

variable {C : Type u} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]
variable {X : TopCat.{w}} {ℱ 𝒢 : X.Sheaf C}

/- The source map lives in the canonical underlying-sheaf functor `sheafCompose`, while
`filteredStalk` and `stalkCompIso` express precisely that each induced map on stalks underlies a
`C`-morphism. Mathlib has no theorem combining these owners into the local-to-global lifting
criterion, so this declaration is the thin source-facing bridge. Uniqueness records the source
claim that the given map itself is a morphism and makes the result directly reusable. -/
/- Lemma 6.16.4: an underlying morphism of sheaves of sets whose induced map on every stalk is
the underlying map of a morphism in `C` comes from a unique morphism of `C`-valued sheaves. -/
@[stacks 007W]
#check TopCat.Sheaf.Algebraic.existsUnique_hom_of_stalkwise F

end
