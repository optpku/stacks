/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Grp.AB
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

universe u

section

variable {X : TopCat.{u}} (ℱ : X.Presheaf AddCommGrpCat)
variable {x : X} {U : Opens X} (hx : x ∈ U)

/- The source's abelian-group structure is already carried by the categorical colimit
`TopCat.Presheaf.stalk`: filtered colimits exist in `AddCommGrpCat`, and
`TopCat.Presheaf.germ` is the canonical morphism from sections into that colimit. Recalling these
owners preserves the source specialization while exposing the more reusable category-valued API. -/

/- Lemma 6.12.1 (1): for an `AddCommGrpCat`-valued presheaf, the germ map is already the canonical
owner morphism `ℱ.germ U x hx : ℱ.obj (op U) ⟶ ℱ.stalk x`. Its additivity is therefore just the
standard `map_add` property of morphisms in `AddCommGrpCat`. -/
@[stacks 007F "germ maps into stalks of abelian presheaves"]
recall TopCat.Presheaf.germ
#check (ℱ.germ U x hx).hom.map_add

/- Lemma 6.12.1 (2): the stalk `ℱ_x` is the colimit of the diagram of sections over open
neighborhoods of `x` in the category of abelian groups. In Lean this owner construction is the
canonical mathlib declaration `TopCat.Presheaf.stalk`, defined as that colimit. -/
@[stacks 007F "stalks as colimits in the category of abelian groups"]
recall TopCat.Presheaf.stalk

end
