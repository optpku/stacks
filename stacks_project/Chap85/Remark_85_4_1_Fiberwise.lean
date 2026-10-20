module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap07.Definition_7_20_1_Cocontinuous
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise

/-!
# Augmentations of fiberwise simplicial sites

An augmentation towards a site `D` in the cocontinuous presentation is a
presenting functor `u0 : F.obj (op ⦋0⦌) ⥤ D` which is cocontinuous and equalizes
all simplex operators `φ : ⦋0⦌ ⟶ n` after precomposition.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Grothendieck

section

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)

variable [h_aug : IsAugmentation F J K u0]
include h_aug

variable [K.IsSite] [(J (op ⦋0⦌)).IsSite]
variable [HasSheafify (J (op ⦋0⦌)).toGrothendieck (Type w)]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0.op.HasPointwiseRightKanExtension P]

/-- The morphism of topoi `a0 : Sh(F.obj (op ⦋0⦌)) ⟶ Sh(D)` presented by `u0`. -/
noncomputable def IsAugmentation.toposMap :
    MorphismOfTopoiIn K.toGrothendieck (J (op ⦋0⦌)).toGrothendieck :=
  u0.morphismOfTopoiInOfCocontinuous (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck

end

end CategoryTheory.Grothendieck
