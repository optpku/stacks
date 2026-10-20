/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Notation
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory TopCat

open scoped TopCat

variable (X : TopCat.{u})

/-
The canonical predicate `TopCat.Presheaf.IsSheaf` is equivalent, for set-valued presheaves, to
`TopCat.Presheaf.IsSheafUniqueGluing`, whose compatibility and gluing predicates expand exactly to
agreement on pairwise intersections and restriction to the given local sections. The canonical
owner `TopCat.Sheaf`, together with `CategoryTheory.Sheaf.homEquiv`, then supplies the full
subcategory and its presheaf-level morphisms; the standard notation `Sh(X)` is owned by the shared
topological sheaf API.
-/

/- Definition 6.7.1 (1): a presheaf of sets is a sheaf exactly when every compatible family of
sections on an open cover has a unique gluing. -/
@[stacks 006T "unique gluing characterization of sheaves of sets"]
#check
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types :
    ∀ F : X.Presheaf (Type v), F.IsSheaf ↔ F.IsSheafUniqueGluing)

section

variable {X}
variable (ℱ 𝒢 : Sh(X))

/- Definition 6.7.1 (2): morphisms of sheaves of sets are morphisms of their underlying
presheaves. -/
@[stacks 006T "morphisms of sheaves are morphisms of underlying presheaves"]
#check (Sheaf.homEquiv : (ℱ ⟶ 𝒢) ≃ (ℱ.presheaf ⟶ 𝒢.presheaf))

end

/- Definition 6.7.1 (3): the category of sheaves of sets on `X` is denoted `Sh(X)`. -/
@[stacks 006T "category of sheaves of sets on a topological space"]
#check (Sh(X))
