/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X U : TopCat.{u}} (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j)

/- Exercise 111.32.5 (1): on sheaves of sets, pullback along an open immersion
has a left adjoint given by extension by the empty set. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.adjunction (C := Type u) hj :
  TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.functor (C := Type u) hj ⊣
    TopCat.Sheaf.pullback (Type u) j)

/- Exercise 111.32.5 (2): the stalk at a point of `U` is canonically isomorphic
to the extended stalk at its image in `X`. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.stalkComparison_isIso (C := Type u) hj :
  ∀ (F : U.Sheaf (Type u)) (x : U),
    IsIso (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.stalkComparison hj F x))

/- Exercise 111.32.5 (3): outside the image of `j`, extension by the empty set
has empty stalks. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.stalk_isEmpty_of_not_mem_range hj :
  ∀ (F : U.Sheaf (Type u)) (x : X), x ∉ Set.range j →
    IsEmpty (((TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.functor
      (C := Type u) hj).obj F).presheaf.stalk x))

end

section

variable {X U : TopCat.{u}} (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j)

/- Exercise 111.32.5 (4): on sheaves of abelian groups, pullback along the
open immersion has a left adjoint given by extension by zero. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.adjunction (C := AddCommGrpCat.{u}) hj :
  TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.functor (C := AddCommGrpCat.{u}) hj ⊣
    TopCat.Sheaf.pullback AddCommGrpCat.{u} j)

/- Exercise 111.32.5 (5): the abelian stalk at a point of `U` is canonically
isomorphic to the extended stalk at its image in `X`. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.stalkComparison_isIso
    (C := AddCommGrpCat.{u}) hj :
  ∀ (F : U.Sheaf AddCommGrpCat.{u}) (x : U),
    IsIso (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.stalkComparison hj F x))

/- Exercise 111.32.5 (6): outside the image of `j`, extension by zero has
zero abelian stalks. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.stalk_isZero_of_not_mem_range hj :
  ∀ (F : U.Sheaf AddCommGrpCat.{u}) (x : X), x ∉ Set.range j →
    CategoryTheory.Limits.IsZero
      (((TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.functor
        (C := AddCommGrpCat.{u}) hj).obj F).presheaf.stalk x))

end

section

variable {X : TopCat.{u}} (U : Opens X)

/- Exercise 111.32.5 (7): extension by the empty set from a proper open
subset is not left exact, so it differs from extension by zero. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.Type.not_leftExact_of_ne_top U :
  U ≠ ⊤ → ¬ CategoryTheory.leftExactFunctor
    ((TopCat.Opens.Subspace.space U).Sheaf (Type u)) (X.Sheaf (Type u))
    (TopCat.Sheaf.ExtensionByInitial.functor (C := Type u) U))

/- Exercise 111.32.5 (8): extension by zero on sheaves of abelian groups is
exact. -/
@[stacks 02EW]
#check (TopCat.Sheaf.ExtensionByInitial.AddCommGrp.exact U :
  CategoryTheory.exactFunctor
    ((TopCat.Opens.Subspace.space U).Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})
    (TopCat.Sheaf.ExtensionByInitial.functor (C := AddCommGrpCat.{u}) U))

end
