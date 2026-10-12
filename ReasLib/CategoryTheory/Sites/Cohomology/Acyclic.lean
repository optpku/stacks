/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Cohomology.Ext
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive

/-!
# Totally acyclic sheaves and section functors

This file connects the site-theoretic notion of total acyclicity with the generic
bounded-below right-acyclicity API for global sections and for sections over a presheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v z

namespace CategoryTheory.Sheaf.IsTotallyAcyclic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{z}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{z})]

/-- Stacks 0731 (3): a totally acyclic abelian sheaf is bounded-below right acyclic for
global sections. -/
@[stacks 0731 "(3), abelian sheaves"]
theorem rightAcyclicForGlobalSections
    (F : Sheaf J AddCommGrpCat.{z}) [IsTotallyAcyclic F] :
    Functor.RightAcyclic.Bounded (Sheaf.Γ J AddCommGrpCat.{z}) F := sorry

section Presheaf

variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max z v}]
variable [HasExt.{max z v} (Sheaf J AddCommGrpCat.{max z v})]

/-- Stacks 0731 (2): a totally acyclic abelian sheaf is bounded-below right acyclic for
sections over every type-valued presheaf. -/
@[stacks 0731 "(2)"]
theorem rightAcyclicForPresheaf
    (G : Cᵒᵖ ⥤ Type (max z v))
    (F : Sheaf J AddCommGrpCat.{max z v}) [IsTotallyAcyclic F] :
    Functor.RightAcyclic.Bounded
      (CohomologyOverPresheaf.homFunctor J G) F := sorry

end Presheaf

end CategoryTheory.Sheaf.IsTotallyAcyclic
