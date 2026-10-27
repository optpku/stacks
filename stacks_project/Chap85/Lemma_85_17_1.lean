/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.SheafDescent

/-!
# Lemma 85.17.1

Let `C` be a site with equalizers and fibre products, and let `K` be a hypercovering.
Then `a⁻¹ : Sh(C) ⥤ Sh((C / K)_total)` is fully faithful with essential image the cartesian
sheaves of sets, `a⁻¹ : Ab(C) ⥤ Ab((C / K)_total)` is fully faithful with essential image
the cartesian sheaves of abelian groups, and in both cases `a_*` is a quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasWeakSheafify J (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) (Type (max w u v))]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type (max w u v),
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/- Lemma 85.17.1 (1): Augmentation inverse image identifies sheaves of sets on the site
with Cartesian sheaves of sets on its hypercovering total site, with direct image as quasi-inverse. -/
@[stacks 0D8E] #check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence J K (Type (max w u v)) :
  Sheaf J (Type (max w u v)) ≌ Cartesian J K.simplicial (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor J K (Type (max w u v)) :
  (cartesianEquivalence J K (Type (max w u v))).functor = cartesianFunctor J K (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse J K (Type (max w u v)) :
  (cartesianEquivalence J K (Type (max w u v))).inverse = cartesianInverse J K (Type (max w u v)))

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_full J K (Type (max w u v)) :
  (inverseImage J K.simplicial (Type (max w u v))).Full)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_faithful J K (Type (max w u v)) :
  (inverseImage J K.simplicial (Type (max w u v))).Faithful)

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian J K (Type (max w u v)) :
  ∀ G : Sheaf (overSiteTotalTopology J K.simplicial) (Type (max w u v)),
    (inverseImage J K.simplicial (Type (max w u v))).essImage G ↔
      IsCartesian J K.simplicial (Type (max w u v)) G)

variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/- Lemma 85.17.1 (2): Augmentation inverse image identifies sheaves of abelian groups on the site
with Cartesian sheaves of abelian groups on its hypercovering total site, with direct image as quasi-inverse. -/
@[stacks 0D8E] #check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence J K AddCommGrpCat.{max w u v} :
  Sheaf J AddCommGrpCat.{max w u v} ≌ Cartesian J K.simplicial AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor J K AddCommGrpCat.{max w u v} :
  (cartesianEquivalence J K AddCommGrpCat.{max w u v}).functor = cartesianFunctor J K AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse J K AddCommGrpCat.{max w u v} :
  (cartesianEquivalence J K AddCommGrpCat.{max w u v}).inverse = cartesianInverse J K AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_full J K AddCommGrpCat.{max w u v} :
  (inverseImage J K.simplicial AddCommGrpCat.{max w u v}).Full)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_faithful J K AddCommGrpCat.{max w u v} :
  (inverseImage J K.simplicial AddCommGrpCat.{max w u v}).Faithful)

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian J K AddCommGrpCat.{max w u v} :
  ∀ G : Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v},
    (inverseImage J K.simplicial AddCommGrpCat.{max w u v}).essImage G ↔
      IsCartesian J K.simplicial AddCommGrpCat.{max w u v} G)

end CategoryTheory.SemiRepresentableFamily
