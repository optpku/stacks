/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Pointwise.BasisSubgroups
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.32.10 (1): restriction-compatible subgroups on a basis define a sheaf of
locally admissible pointwise tuples. -/
@[stacks 0790] #check
  (TopCat.Presheaf.PointwiseProduct.BasisSubgroups.isSheaf :
    ∀ {X : TopCat.{u}} {A : X → AddCommGrpCat.{u}}
      (S : TopCat.Presheaf.PointwiseProduct.BasisSubgroups A), S.presheaf.IsSheaf)

/- Exercise 111.32.10 (2): on the discrete two-point space with integer fibres, trivial
subgroup on the whole space and full subgroups on proper opens, local sections on the whole
space need not equal the assigned subgroup. -/
@[stacks 0790] #check
  (TopCat.Presheaf.PointwiseProduct.finTwo_univ_ne :
    TopCat.Presheaf.PointwiseProduct.finTwoBasisSubgroups.sectionSubgroup ⊤ ≠
      TopCat.Presheaf.PointwiseProduct.finTwoBasisSubgroups.subgroup ⊤ (Set.mem_univ ⊤))

end
