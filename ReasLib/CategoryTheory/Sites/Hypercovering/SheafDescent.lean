/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Slice
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.SheafDescent
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Sheaf descent along a hypercovering of an object

Sheaves of sets and of abelian groups on a slice site are equivalent to cartesian
sheaves on the total site of a hypercovering of the sliced object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasWeakSheafify (J.over X) (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    (Type (max w u v))]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    Type (max w u v),
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Augmentation inverse image identifies sheaves of sets on the slice site with
cartesian sheaves on the total site of a hypercovering, with direct image as inverse. -/
def sheafCartesianEquivalence :
    Sheaf (J.over X) (Type (max w u v)) ≌
      Cartesian (J.over X) K.toSimplicialObject (Type (max w u v)) :=
  SemiRepresentableFamily.cartesianEquivalence.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) (Type (max w u v))

variable [HasWeakSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Augmentation inverse image identifies sheaves of abelian groups on the slice site
with cartesian sheaves on the total site of a hypercovering, with direct image as inverse. -/
def abelianCartesianEquivalence :
    Sheaf (J.over X) AddCommGrpCat.{max w u v} ≌
      Cartesian (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v} :=
  SemiRepresentableFamily.cartesianEquivalence.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v}

end CategoryTheory.Hypercovering
