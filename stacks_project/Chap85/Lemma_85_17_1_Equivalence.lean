/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.SheafDescent

/-!
# Hypercovering descent equivalence for sheaves

If `K` is a hypercovering of the terminal presheaf, then `a⁻¹ : Sh(C) ⥤ Sh((C / K)_total)`
is fully faithful with essential image the cartesian sheaves, and `a_*` is a quasi-inverse.
The same statement holds for abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable (A : Type (max w u v + 1)) [Category.{max w u v} A]
variable [HasWeakSheafify J A]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ A,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.SemiRepresentableFamily.sheafLocalizationAdjunction J K A :
  inverseImage J K.simplicial A ⊣ directImage J K.simplicial A)

#check (CategoryTheory.SemiRepresentableFamily.sheafLocalizationAdjunction_eq J K A :
  sheafLocalizationAdjunction J K A =
    (totalForget K.simplicial).sheafAdjunctionCocontinuous A
      (overSiteTotalTopology J K.simplicial) J)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_full J K A :
  (inverseImage J K.simplicial A).Full)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_faithful J K A :
  (inverseImage J K.simplicial A).Faithful)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_fullyFaithful J K A :
  (inverseImage J K.simplicial A).FullyFaithful)

#check (CategoryTheory.SemiRepresentableFamily.unit_app_isIso J K A :
  ∀ F : Sheaf J A, IsIso ((sheafLocalizationAdjunction J K A).unit.app F))

#check (CategoryTheory.SemiRepresentableFamily.counit_app_isIso_iff_isCartesian J K A :
  ∀ G : Sheaf (overSiteTotalTopology J K.simplicial) A,
    IsIso ((sheafLocalizationAdjunction J K A).counit.app G) ↔ IsCartesian J K.simplicial A G)

#check (CategoryTheory.SemiRepresentableFamily.counit_app_isIso_of_isCartesian J K A :
  ∀ G : Sheaf (overSiteTotalTopology J K.simplicial) A,
    IsCartesian J K.simplicial A G → IsIso ((sheafLocalizationAdjunction J K A).counit.app G))

#check (CategoryTheory.SemiRepresentableFamily.mem_essImage_iff_isCartesian J K A :
  ∀ G : Sheaf (overSiteTotalTopology J K.simplicial) A,
    (inverseImage J K.simplicial A).essImage G ↔ IsCartesian J K.simplicial A G)

#check (CategoryTheory.SemiRepresentableFamily.cartesianFunctor J K A :
  Sheaf J A ⥤ Cartesian J K.simplicial A)

#check (CategoryTheory.SemiRepresentableFamily.cartesianFunctor_obj J K A :
  ∀ F : Sheaf J A,
    ((cartesianFunctor J K A).obj F).obj = (inverseImage J K.simplicial A).obj F)

#check (CategoryTheory.SemiRepresentableFamily.cartesianInverse J K A :
  Cartesian J K.simplicial A ⥤ Sheaf J A)

#check (CategoryTheory.SemiRepresentableFamily.cartesianInverse_obj J K A :
  ∀ G : Cartesian J K.simplicial A,
    (cartesianInverse J K A).obj G = (directImage J K.simplicial A).obj G.obj)

#check (CategoryTheory.SemiRepresentableFamily.cartesianUnitIso J K A :
  𝟭 (Sheaf J A) ≅ cartesianFunctor J K A ⋙ cartesianInverse J K A)

#check (CategoryTheory.SemiRepresentableFamily.cartesianUnitIso_hom_app J K A :
  ∀ F : Sheaf J A,
    (cartesianUnitIso J K A).hom.app F = (sheafLocalizationAdjunction J K A).unit.app F)

#check (CategoryTheory.SemiRepresentableFamily.cartesianCounitIso J K A :
  cartesianInverse J K A ⋙ cartesianFunctor J K A ≅ 𝟭 (Cartesian J K.simplicial A))

#check (CategoryTheory.SemiRepresentableFamily.cartesianCounitIso_hom_app_hom J K A :
  ∀ G : Cartesian J K.simplicial A,
    ((cartesianCounitIso J K A).hom.app G).hom =
      (sheafLocalizationAdjunction J K A).counit.app G.obj)

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence J K A :
  Sheaf J A ≌ Cartesian J K.simplicial A)

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_functor J K A :
  (cartesianEquivalence J K A).functor = cartesianFunctor J K A)

#check (CategoryTheory.SemiRepresentableFamily.cartesianEquivalence_inverse J K A :
  (cartesianEquivalence J K A).inverse = cartesianInverse J K A)

end CategoryTheory.SemiRepresentableFamily
