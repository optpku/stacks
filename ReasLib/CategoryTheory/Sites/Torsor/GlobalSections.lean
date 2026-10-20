/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.Basic
public import ReasLib.CategoryTheory.Sites.GlobalSections.Terminal
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsor triviality and global sections

This leaf owns the site-generic criterion that a torsor is trivial exactly when its sheaf of
sections has a global section.  The proof-facing directions are named separately so downstream
arguments can use the implication they need without unpacking a torsor isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}}
variable [HasWeakSheafify J (Type w)]
variable [HasGlobalSectionsFunctor J (Type w)]

/-- A global section of a torsor supplies its canonical translation trivialization. -/
@[stacks 03AI "torsor triviality from a global section"]
theorem isTrivial_of_nonempty_globalSections
    (P : Torsor G) (hs : Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier)) :
    P.IsTrivial := sorry

/-- A trivial torsor has a global section, obtained by transporting the identity section of the
trivial torsor across an inverse torsor isomorphism. -/
@[stacks 03AI "global section of a trivial torsor"]
theorem nonempty_globalSections_of_isTrivial
    (P : Torsor G) (hP : P.IsTrivial) :
    Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier) := sorry

/-- Lemma 21.4.2 (03AI): a torsor is trivial if and only if its sheaf of sections has a nonempty
set of global sections. -/
@[stacks 03AI "torsor triviality criterion"]
theorem isTrivial_iff_nonempty_globalSections (P : Torsor G) :
    P.IsTrivial ↔ Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier) := sorry

end CategoryTheory.Sheaf.Torsor
