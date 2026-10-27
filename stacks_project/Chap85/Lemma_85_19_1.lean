/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.SheafDescent

/-!
# Hypercovering descent on a slice site

Augmentation inverse image identifies sheaves on the slice with cartesian sheaves
on the total site, with augmentation direct image as quasi-inverse.
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

/- Lemma 85.19.1 (1): Augmentation inverse image is fully faithful with essential
image the cartesian sheaves of sets; direct image is its quasi-inverse. -/
@[stacks 0D8K] #check (CategoryTheory.Hypercovering.sheafCartesianEquivalence J X K :
  Sheaf (J.over X) (Type (max w u v)) ≌
    Cartesian (J.over X) K.toSimplicialObject (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) (Type (max w u v)) :
  (sheafCartesianEquivalence J X K).functor =
    CategoryTheory.SemiRepresentableFamily.cartesianFunctor.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) (Type (max w u v)) :
  (sheafCartesianEquivalence J X K).inverse =
    CategoryTheory.SemiRepresentableFamily.cartesianInverse.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianFunctor_obj.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) (Type (max w u v)) :
  ∀ F : Sheaf (J.over X) (Type (max w u v)),
    ((sheafCartesianEquivalence J X K).functor.obj F).obj =
      (inverseImage (J.over X) K.toSimplicialObject (Type (max w u v))).obj F)

#check (CategoryTheory.SemiRepresentableFamily.cartesianInverse_obj.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) (Type (max w u v)) :
  ∀ G : Cartesian (J.over X) K.toSimplicialObject (Type (max w u v)),
    (sheafCartesianEquivalence J X K).inverse.obj G =
      (directImage (J.over X) K.toSimplicialObject (Type (max w u v))).obj G.obj)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_fullyFaithful.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) (Type (max w u v)) :
  (inverseImage (J.over X) K.toSimplicialObject (Type (max w u v))).FullyFaithful)

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) (Type (max w u v)) :
  ∀ G : Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject) (Type (max w u v)),
    (inverseImage (J.over X) K.toSimplicialObject (Type (max w u v))).essImage G ↔
      IsCartesian (J.over X) K.toSimplicialObject (Type (max w u v)) G)

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

/- Lemma 85.19.1 (2): Augmentation inverse image is fully faithful with essential
image the cartesian sheaves of abelian groups; direct image is its quasi-inverse. -/
@[stacks 0D8K] #check (CategoryTheory.Hypercovering.abelianCartesianEquivalence J X K :
  Sheaf (J.over X) AddCommGrpCat.{max w u v} ≌
    Cartesian (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v} :
  (abelianCartesianEquivalence J X K).functor =
    CategoryTheory.SemiRepresentableFamily.cartesianFunctor.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v} :
  (abelianCartesianEquivalence J X K).inverse =
    CategoryTheory.SemiRepresentableFamily.cartesianInverse.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianFunctor_obj.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v} :
  ∀ F : Sheaf (J.over X) AddCommGrpCat.{max w u v},
    ((abelianCartesianEquivalence J X K).functor.obj F).obj =
      (inverseImage (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v}).obj F)

#check (CategoryTheory.SemiRepresentableFamily.cartesianInverse_obj.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v} :
  ∀ G : Cartesian (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v},
    (abelianCartesianEquivalence J X K).inverse.obj G =
      (directImage (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v}).obj G.obj)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_fullyFaithful.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v} :
  (inverseImage (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v}).FullyFaithful)

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) AddCommGrpCat.{max w u v} :
  ∀ G : Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject) AddCommGrpCat.{max w u v},
    (inverseImage (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v}).essImage G ↔
      IsCartesian (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v} G)

end CategoryTheory.Hypercovering
