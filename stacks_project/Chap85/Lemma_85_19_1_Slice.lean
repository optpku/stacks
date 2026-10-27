/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Slice
public import ReasLib.CategoryTheory.Sites.Hypercovering.SheafDescent

/-!
# Slice hypercovering descent compatibility

The slice conversion and descent API are supplied by their mathematical owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)

variable (A : Type (max w u v + 1)) [Category.{max w u v} A]
variable [HasWeakSheafify (J.over X) A]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject) A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ A,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.Hypercovering.toSliceTerminal J X K :
  HypercoveringOf.Terminal.{w} (J.over X))

#check (CategoryTheory.Hypercovering.toSliceTerminal_simplicial J X K :
  (toSliceTerminal J X K).simplicial = K.toSimplicialObject)

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A :
  Sheaf (J.over X) A ≌ Cartesian (J.over X) K.toSimplicialObject A)

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A :
  (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) A).functor =
    CategoryTheory.SemiRepresentableFamily.cartesianFunctor.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) A)

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A :
  (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) A).inverse =
    CategoryTheory.SemiRepresentableFamily.cartesianInverse.{w, v, max u v}
      (J.over X) (toSliceTerminal J X K) A)

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A :
  ∀ G : Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject) A,
    (inverseImage (J.over X) K.toSimplicialObject A).essImage G ↔
      IsCartesian (J.over X) K.toSimplicialObject A G)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_full.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A :
  (inverseImage (J.over X) K.toSimplicialObject A).Full)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_faithful.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A :
  (inverseImage (J.over X) K.toSimplicialObject A).Faithful)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_fullyFaithful.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A :
  (inverseImage (J.over X) K.toSimplicialObject A).FullyFaithful)

end CategoryTheory.Hypercovering
