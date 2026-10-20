module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram

/-!
# Augmentations of covariant simplicial diagrams of sites

An augmentation towards a site `D` in the morphism-of-sites presentation is a
presenting functor `u0 : D ⥤ C.obj ⦋0⦌` which is an exact morphism of sites and
equalizes all simplex operators `φ : ⦋0⦌ ⟶ n`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialSites

section

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify (J ⦋0⦌).toGrothendieck (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]

variable [h_aug : IsAugmentation C J K u0]
include h_aug

/-- The morphism of topoi `a0 : Sh(C.obj ⦋0⦌) ⟶ Sh(D)` presented by `u0`. -/
noncomputable def IsAugmentation.toposMap :
    MorphismOfTopoiIn K.toGrothendieck (J ⦋0⦌).toGrothendieck :=
  u0.morphismOfTopoiInOfContinuous K.toGrothendieck (J ⦋0⦌).toGrothendieck

end

end CategoryTheory.SimplicialSites
