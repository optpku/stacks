/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.CategoryTheory.Sites.Hypercovering.SheafDescent
import StacksCheckRecall

/-!
# Lemma 85.21.1

Let `C` be a site with fibre products and `X` an object of `C`. Let `a : U ⟶ X`
be a hypercovering of `X` in `C`. Then `a⁻¹ : Sh(C / X) ⥤ Sh((C / U)_total)` is
fully faithful with essential image the cartesian sheaves of sets,
`a⁻¹ : Ab(C / X) ⥤ Ab((C / U)_total)` is fully faithful with essential image the
cartesian sheaves of abelian groups, and in both cases `a_*` is a quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
variable (hA : A.IsHypercovering J)
variable [HasWeakSheafify (J.over A.right) (Type (max w u v))]
variable [HasWeakSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    (Type (max w u v))]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over A.right)
          (toHypercovering.{w} A hA).toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
      Type (max w u v),
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]

/- Lemma 85.21.1 (1): Augmentation inverse image is fully faithful with essential
image the cartesian sheaves of sets; direct image is its quasi-inverse. -/
@[stacks 0DA8] #check (CategoryTheory.Hypercovering.sheafCartesianEquivalence J A.right (toHypercovering.{w} A hA) :
  Sheaf (J.over A.right) (Type (max w u v)) ≌
    Cartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)) :
  (CategoryTheory.Hypercovering.sheafCartesianEquivalence J A.right (toHypercovering.{w} A hA)).functor =
    CategoryTheory.SemiRepresentableFamily.cartesianFunctor.{w, v, max u v}
      (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)) :
  (CategoryTheory.Hypercovering.sheafCartesianEquivalence J A.right (toHypercovering.{w} A hA)).inverse =
    CategoryTheory.SemiRepresentableFamily.cartesianInverse.{w, v, max u v}
      (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianFunctor_obj.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)) :
  ∀ F : Sheaf (J.over A.right) (Type (max w u v)),
    ((CategoryTheory.Hypercovering.sheafCartesianEquivalence J A.right (toHypercovering.{w} A hA)).functor.obj F).obj =
      (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject (Type (max w u v))).obj F)

#check (CategoryTheory.SemiRepresentableFamily.cartesianInverse_obj.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)) :
  ∀ G : Cartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject (Type (max w u v)),
    (CategoryTheory.Hypercovering.sheafCartesianEquivalence J A.right (toHypercovering.{w} A hA)).inverse.obj G =
      (directImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject (Type (max w u v))).obj G.obj)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_fullyFaithful.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)) :
  (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject (Type (max w u v))).FullyFaithful)

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) (Type (max w u v)) :
  ∀ G : Sheaf (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject) (Type (max w u v)),
    (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject (Type (max w u v))).essImage G ↔
      IsCartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject (Type (max w u v)) G)

variable [HasWeakSheafify (J.over A.right) AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over A.right)
          (toHypercovering.{w} A hA).toSimplicialObject n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
      AddCommGrpCat.{max w u v},
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]

/- Lemma 85.21.1 (2): Augmentation inverse image is fully faithful with essential
image the cartesian sheaves of abelian groups; direct image is its quasi-inverse. -/
@[stacks 0DA8] #check (CategoryTheory.Hypercovering.abelianCartesianEquivalence J A.right (toHypercovering.{w} A hA) :
  Sheaf (J.over A.right) AddCommGrpCat.{max w u v} ≌
    Cartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v} :
  (CategoryTheory.Hypercovering.abelianCartesianEquivalence J A.right (toHypercovering.{w} A hA)).functor =
    CategoryTheory.SemiRepresentableFamily.cartesianFunctor.{w, v, max u v}
      (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v} :
  (CategoryTheory.Hypercovering.abelianCartesianEquivalence J A.right (toHypercovering.{w} A hA)).inverse =
    CategoryTheory.SemiRepresentableFamily.cartesianInverse.{w, v, max u v}
      (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianFunctor_obj.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v} :
  ∀ F : Sheaf (J.over A.right) AddCommGrpCat.{max w u v},
    ((CategoryTheory.Hypercovering.abelianCartesianEquivalence J A.right (toHypercovering.{w} A hA)).functor.obj F).obj =
      (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject AddCommGrpCat.{max w u v}).obj F)

#check (CategoryTheory.SemiRepresentableFamily.cartesianInverse_obj.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v} :
  ∀ G : Cartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject AddCommGrpCat.{max w u v},
    (CategoryTheory.Hypercovering.abelianCartesianEquivalence J A.right (toHypercovering.{w} A hA)).inverse.obj G =
      (directImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject AddCommGrpCat.{max w u v}).obj G.obj)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_fullyFaithful.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v} :
  (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject AddCommGrpCat.{max w u v}).FullyFaithful)

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)) AddCommGrpCat.{max w u v} :
  ∀ G : Sheaf (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject) AddCommGrpCat.{max w u v},
    (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject AddCommGrpCat.{max w u v}).essImage G ↔
      IsCartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject AddCommGrpCat.{max w u v} G)

end CategoryTheory.SimplicialObject.Augmented
